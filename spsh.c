#define _XOPEN_SOURCE 700
#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <pty.h>
#include <sys/ioctl.h>
#include <sys/select.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <termios.h>
#include <signal.h>
#include <vterm.h>
#include <errno.h>

typedef struct {
    VTermScreenCell *cells;
    int cols;
} ScrollbackLine;

typedef struct {
    int hist_id;
    ScrollbackLine *lines;
    int line_cnt;
    int line_cap;
} CommandHistory;

#define CMD_MAX 2000
static CommandHistory cmds[CMD_MAX];
static int cmds_cnt = 0;

static int cur_hist_id = -1;
static CommandHistory *cur_cmd = NULL;
static int view_hist_id = -1;

static VTerm *vt;
static VTermScreen *vts;
static VTermState *vts_state;

static int T_rows = 24, T_cols = 80;
static int mfd = -1;
static pid_t cpid = -1;
static char zdotdir[256];
static struct termios orig_t;

static volatile sig_atomic_t sig_winch = 0, sig_chld = 0;

static int in_prompt = 0;
static int max_cursor_row = 0;
static int scroll_offset = 0;
static int input_scroll_offset = 0;
static int dirty = 0;
static int is_altscreen = 0;

static ScrollbackLine *prompt_lines = NULL;
static int prompt_line_cnt = 0;
static int prompt_line_cap = 0;

static void handle_winch(int s) { (void)s; sig_winch = 1; }
static void handle_chld(int s) { (void)s; sig_chld = 1; }

static int on_sb_pushline(int cols, const VTermScreenCell *cells, void *user) {
    if (!is_altscreen) {
        if (in_prompt) {
            if (prompt_line_cnt >= prompt_line_cap) {
                prompt_line_cap = prompt_line_cap ? prompt_line_cap * 2 : 64;
                prompt_lines = realloc(prompt_lines, prompt_line_cap * sizeof(ScrollbackLine));
            }
            ScrollbackLine *sbl = &prompt_lines[prompt_line_cnt++];
            sbl->cols = cols;
            sbl->cells = malloc(cols * sizeof(VTermScreenCell));
            memcpy(sbl->cells, cells, cols * sizeof(VTermScreenCell));
            if (input_scroll_offset > 0) input_scroll_offset++;
        } else if (cur_cmd) {
            if (cur_cmd->line_cnt >= cur_cmd->line_cap) {
                cur_cmd->line_cap = cur_cmd->line_cap ? cur_cmd->line_cap * 2 : 64;
                cur_cmd->lines = realloc(cur_cmd->lines, cur_cmd->line_cap * sizeof(ScrollbackLine));
            }
            ScrollbackLine *sbl = &cur_cmd->lines[cur_cmd->line_cnt++];
            sbl->cols = cols;
            sbl->cells = malloc(cols * sizeof(VTermScreenCell));
            memcpy(sbl->cells, cells, cols * sizeof(VTermScreenCell));
        }
    }
    return 1;
}

static int on_bell(void *user) {
    printf("\a"); fflush(stdout);
    return 1;
}

static int on_damage(VTermRect rect, void *user) {
    dirty = 1; return 1;
}

static int on_movecursor(VTermPos pos, VTermPos oldpos, int visible, void *user) {
    if (pos.row > max_cursor_row) max_cursor_row = pos.row;
    dirty = 1; return 1;
}

static int on_settermprop(VTermProp prop, VTermValue *val, void *user) {
    if (prop == VTERM_PROP_ALTSCREEN) is_altscreen = val->boolean;
    dirty = 1; return 1;
}

static VTermScreenCallbacks cb_screen = {
    .damage = on_damage,
    .moverect = NULL,
    .movecursor = on_movecursor,
    .settermprop = on_settermprop,
    .bell = on_bell,
    .resize = NULL,
    .sb_pushline = on_sb_pushline,
    .sb_popline = NULL,
};

static void term_size(void) {
    struct winsize w;
    if (ioctl(STDIN_FILENO, TIOCGWINSZ, &w) == 0) { T_rows = w.ws_row; T_cols = w.ws_col; }
}

static void term_raw(void) {
    tcgetattr(STDIN_FILENO, &orig_t);
    struct termios t = orig_t;
    t.c_lflag &= ~(ECHO | ICANON | ISIG | IEXTEN);
    t.c_iflag &= ~(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
    t.c_oflag &= ~OPOST;
    t.c_cflag |= CS8;
    t.c_cc[VMIN] = 1; t.c_cc[VTIME] = 0;
    tcsetattr(STDIN_FILENO, TCSAFLUSH, &t);
}

static void term_restore(void) {
    tcsetattr(STDIN_FILENO, TCSAFLUSH, &orig_t);
}

static int utf8_encode(uint32_t codepoint, char *out) {
    if (codepoint < 0x80) { out[0] = codepoint; return 1; }
    else if (codepoint < 0x800) { out[0] = 0xC0 | (codepoint >> 6); out[1] = 0x80 | (codepoint & 0x3F); return 2; }
    else if (codepoint < 0x10000) { out[0] = 0xE0 | (codepoint >> 12); out[1] = 0x80 | ((codepoint >> 6) & 0x3F); out[2] = 0x80 | (codepoint & 0x3F); return 3; }
    else { out[0] = 0xF0 | (codepoint >> 18); out[1] = 0x80 | ((codepoint >> 12) & 0x3F); out[2] = 0x80 | ((codepoint >> 6) & 0x3F); out[3] = 0x80 | (codepoint & 0x3F); return 4; }
}

static void print_cell(VTermScreenCell *c, VTermScreenCell *p) {
    if (!p || c->attrs.bold != p->attrs.bold ||
        c->attrs.underline != p->attrs.underline ||
        c->attrs.italic != p->attrs.italic ||
        c->attrs.reverse != p->attrs.reverse ||
        !vterm_color_is_equal(&c->fg, &p->fg) ||
        !vterm_color_is_equal(&c->bg, &p->bg)) {
        
        printf("\033[0");
        if (c->attrs.bold) printf(";1");
        if (c->attrs.underline) printf(";4");
        if (c->attrs.italic) printf(";3");
        if (c->attrs.reverse) printf(";7");
        
        if (VTERM_COLOR_IS_RGB(&c->fg)) {
            printf(";38;2;%d;%d;%d", c->fg.rgb.red, c->fg.rgb.green, c->fg.rgb.blue);
        } else if (VTERM_COLOR_IS_INDEXED(&c->fg)) {
            printf(";38;5;%d", c->fg.indexed.idx);
        }
        
        if (VTERM_COLOR_IS_RGB(&c->bg)) {
            printf(";48;2;%d;%d;%d", c->bg.rgb.red, c->bg.rgb.green, c->bg.rgb.blue);
        } else if (VTERM_COLOR_IS_INDEXED(&c->bg)) {
            printf(";48;5;%d", c->bg.indexed.idx);
        }
        printf("m");
    }
    
    if (c->chars[0] == 0) {
        printf(" ");
    } else {
        for (int i = 0; i < VTERM_MAX_CHARS_PER_CELL && c->chars[i]; i++) {
            char bytes[6];
            int len = utf8_encode(c->chars[i], bytes);
            fwrite(bytes, 1, len, stdout);
        }
    }
}

static void capture_vterm_output() {
    if (!cur_cmd) return;
    int rows = max_cursor_row + 1;
    if (rows > T_rows) rows = T_rows;
    
    while (rows > 0) {
        int empty = 1;
        for (int c = 0; c < T_cols; c++) {
            VTermScreenCell cell;
            vterm_screen_get_cell(vts, (VTermPos){rows - 1, c}, &cell);
            if (cell.chars[0] != 0 && cell.chars[0] != ' ') {
                empty = 0; break;
            }
        }
        if (!empty) break;
        rows--;
    }
    
    for (int r = 0; r < rows; r++) {
        if (cur_cmd->line_cnt >= cur_cmd->line_cap) {
            cur_cmd->line_cap = cur_cmd->line_cap ? cur_cmd->line_cap * 2 : 64;
            cur_cmd->lines = realloc(cur_cmd->lines, cur_cmd->line_cap * sizeof(ScrollbackLine));
        }
        ScrollbackLine *sbl = &cur_cmd->lines[cur_cmd->line_cnt++];
        sbl->cols = T_cols;
        sbl->cells = malloc(T_cols * sizeof(VTermScreenCell));
        for (int c = 0; c < T_cols; c++) {
            vterm_screen_get_cell(vts, (VTermPos){r, c}, &sbl->cells[c]);
        }
    }
}

static void start_new_command(int hist_id) {
    cur_cmd = NULL;
    for (int i = 0; i < cmds_cnt; i++) {
        if (cmds[i].hist_id == hist_id) {
            cur_cmd = &cmds[i];
            cur_cmd->line_cnt = 0; // reset
            break;
        }
    }
    if (!cur_cmd) {
        if (cmds_cnt < CMD_MAX) {
            cur_cmd = &cmds[cmds_cnt++];
        } else {
            cur_cmd = &cmds[0]; // overwrite oldest
        }
        cur_cmd->hist_id = hist_id;
        cur_cmd->line_cnt = 0;
        cur_cmd->line_cap = 64;
        cur_cmd->lines = malloc(64 * sizeof(ScrollbackLine));
    }
    cur_hist_id = hist_id;
}

static CommandHistory *get_view_cmd() {
    if (cmds_cnt == 0) return NULL;
    if (view_hist_id == -1) return &cmds[cmds_cnt - 1];
    for (int i = 0; i < cmds_cnt; i++) {
        if (cmds[i].hist_id == view_hist_id) return &cmds[i];
    }
    if (view_hist_id >= cmds[cmds_cnt - 1].hist_id) return &cmds[cmds_cnt - 1];
    return NULL;
}

static void draw(void) {
    if (T_rows < 1) return;
    
    int h_in = 0, sep = 0;
    int total_in = in_prompt ? prompt_line_cnt + max_cursor_row + 1 : 0;
    if (!is_altscreen && in_prompt) {
        h_in = total_in;
        if (h_in > T_rows * 0.7) h_in = T_rows * 0.7;
        if (h_in < 1) h_in = 1;
        sep = 1;
    }
    
    int h_out = T_rows - h_in - sep;
    if (h_out < 0) h_out = 0;
    
    CommandHistory *vc = get_view_cmd();
    int out_lines = vc ? vc->line_cnt : 0;
    
    if (!in_prompt && !is_altscreen) {
        out_lines = (cur_cmd ? cur_cmd->line_cnt : 0) + max_cursor_row + 1;
    }
    if (is_altscreen) out_lines = T_rows; 

    int max_sc = out_lines - h_out;
    if (max_sc < 0) max_sc = 0;
    if (scroll_offset > max_sc) scroll_offset = max_sc;
    if (scroll_offset < 0) scroll_offset = 0;
    
    printf("\033[?25l");
    
    for (int r = 0; r < h_out; r++) {
        printf("\033[%d;1H\033[2K\033[0m", r + 1);
        
        if (is_altscreen) {
            VTermScreenCell prev_cell = {0};
            for (int c = 0; c < T_cols; c++) {
                VTermScreenCell cell;
                vterm_screen_get_cell(vts, (VTermPos){r, c}, &cell);
                print_cell(&cell, &prev_cell);
                prev_cell = cell;
            }
            continue;
        }
        
        int idx_from_bottom = h_out - 1 - r + scroll_offset;
        int line_idx = out_lines - 1 - idx_from_bottom;
        
        if (line_idx >= 0 && line_idx < out_lines) {
            VTermScreenCell prev_cell = {0};
            
            if (!in_prompt && cur_cmd) {
                if (line_idx < cur_cmd->line_cnt) {
                    ScrollbackLine *sbl = &cur_cmd->lines[line_idx];
                    for (int c = 0; c < sbl->cols && c < T_cols; c++) {
                        print_cell(&sbl->cells[c], &prev_cell);
                        prev_cell = sbl->cells[c];
                    }
                } else {
                    int vt_row = line_idx - cur_cmd->line_cnt;
                    for (int c = 0; c < T_cols; c++) {
                        VTermScreenCell cell;
                        vterm_screen_get_cell(vts, (VTermPos){vt_row, c}, &cell);
                        print_cell(&cell, &prev_cell);
                        prev_cell = cell;
                    }
                }
            } else if (vc) {
                if (line_idx < vc->line_cnt) {
                    ScrollbackLine *sbl = &vc->lines[line_idx];
                    for (int c = 0; c < sbl->cols && c < T_cols; c++) {
                        print_cell(&sbl->cells[c], &prev_cell);
                        prev_cell = sbl->cells[c];
                    }
                }
            }
        }
    }
    
    if (sep) {
        printf("\033[%d;1H\033[2K\033[38;5;239m", h_out + 1);
        for(int c=0; c<T_cols; c++) printf("\xe2\x94\x80");
        printf("\033[0m");
    }
    
    if (h_in > 0 && !is_altscreen) {
        int max_in_sc = total_in - h_in;
        if (max_in_sc < 0) max_in_sc = 0;
        if (input_scroll_offset > max_in_sc) input_scroll_offset = max_in_sc;
        if (input_scroll_offset < 0) input_scroll_offset = 0;
        
        for (int r = 0; r < h_in; r++) {
            printf("\033[%d;1H\033[2K\033[0m", h_out + sep + r + 1);
            
            int idx_from_bottom = h_in - 1 - r + input_scroll_offset;
            int line_idx = total_in - 1 - idx_from_bottom;
            
            if (line_idx >= 0 && line_idx < total_in) {
                VTermScreenCell prev_cell = {0};
                if (line_idx < prompt_line_cnt) {
                    ScrollbackLine *sbl = &prompt_lines[line_idx];
                    for (int c = 0; c < sbl->cols && c < T_cols; c++) {
                        print_cell(&sbl->cells[c], &prev_cell);
                        prev_cell = sbl->cells[c];
                    }
                } else {
                    int vt_row = line_idx - prompt_line_cnt;
                    for (int c = 0; c < T_cols; c++) {
                        VTermScreenCell cell;
                        vterm_screen_get_cell(vts, (VTermPos){vt_row, c}, &cell);
                        print_cell(&cell, &prev_cell);
                        prev_cell = cell;
                    }
                }
            }
        }
    }
    
    VTermPos pos;
    vterm_state_get_cursorpos(vts_state, &pos);
    
    int phys_r = -1;
    if (is_altscreen) {
        phys_r = pos.row;
    } else if (!in_prompt) {
        int line_idx = (cur_cmd ? cur_cmd->line_cnt : 0) + pos.row;
        int idx_from_bottom = out_lines - 1 - line_idx;
        phys_r = h_out - 1 - idx_from_bottom + scroll_offset;
    } else {
        int line_idx = prompt_line_cnt + pos.row;
        int idx_from_bottom = total_in - 1 - line_idx;
        int r = h_in - 1 + input_scroll_offset - idx_from_bottom;
        phys_r = h_out + sep + r;
    }
    
    if ((is_altscreen && phys_r >= 0 && phys_r < T_rows) ||
        (!in_prompt && phys_r >= 0 && phys_r < h_out) ||
        (in_prompt && phys_r >= h_out + sep && phys_r < T_rows)) {
        printf("\033[%d;%dH", phys_r + 1, pos.col + 1);
        printf("\033[?25h"); 
    }
    
    fflush(stdout);
    dirty = 0;
}

static int apc_state = 0;
static char apc_buf[256];
static int apc_len = 0;

static void proc_pty_byte(unsigned char c) {
    vterm_input_write(vt, (const char *)&c, 1);
    
    switch (apc_state) {
        case 0: if (c == '\033') apc_state = 1; break;
        case 1:
            if (c == '_') { apc_state = 2; apc_len = 0; }
            else if (c != '\033') apc_state = 0;
            break;
        case 2:
            if (c == '\033') apc_state = 3;
            else if (apc_len < 255) apc_buf[apc_len++] = c;
            break;
        case 3:
            if (c == '\\') {
                apc_state = 0; apc_buf[apc_len] = '\0';
                if (strncmp(apc_buf, "PS:", 3) == 0) {
                    if (!in_prompt) {
                        capture_vterm_output();
                    }
                    vterm_screen_reset(vts, 1);
                    max_cursor_row = 0;
                    in_prompt = 1; scroll_offset = 0; input_scroll_offset = 0;
                    view_hist_id = -1;
                    for (int i=0; i<prompt_line_cnt; i++) free(prompt_lines[i].cells);
                    prompt_line_cnt = 0;
                } else if (strncmp(apc_buf, "CS:", 3) == 0) {
                    int histcmd = atoi(apc_buf + 3);
                    start_new_command(histcmd);
                    in_prompt = 0; scroll_offset = 0; input_scroll_offset = 0;
                    vterm_screen_reset(vts, 1);
                    max_cursor_row = 0;
                } else if (strncmp(apc_buf, "NAV:", 4) == 0) {
                    int histno = atoi(apc_buf + 4);
                    view_hist_id = histno;
                }
                dirty = 1;
            } else if (c == '\033') {
                if (apc_len < 255) apc_buf[apc_len++] = '\033';
            } else {
                if (apc_len < 255) apc_buf[apc_len++] = '\033';
                if (apc_len < 255) apc_buf[apc_len++] = c;
                apc_state = 2;
            }
            break;
    }
}

static void handle_input(const unsigned char *buf, int n) {
    int consumed = 0;
    int wrote_real_input = 0;
    while (consumed < n) {
        if (!is_altscreen && (n - consumed) >= 6 && buf[consumed] == '\033' && buf[consumed+1] == '[' && buf[consumed+2] == '<') {
            int btn, mx, my; char fin;
            int n_read = 0;
            if (sscanf((char *)buf + consumed + 3, "%d;%d;%d%c%n", &btn, &mx, &my, &fin, &n_read) >= 4) {
                if (fin == 'M' || fin == 'm') {
                    if (btn == 64) {
                        int h_in = in_prompt ? prompt_line_cnt + max_cursor_row + 1 : 0;
                        if (h_in > T_rows * 0.7) h_in = T_rows * 0.7;
                        if (h_in < 1) h_in = 1;
                        int h_out = T_rows - h_in - (in_prompt ? 1 : 0);
                        if (my <= h_out) scroll_offset += 3;
                        else input_scroll_offset += 3;
                        dirty = 1;
                    }
                    else if (btn == 65) {
                        int h_in = in_prompt ? prompt_line_cnt + max_cursor_row + 1 : 0;
                        if (h_in > T_rows * 0.7) h_in = T_rows * 0.7;
                        if (h_in < 1) h_in = 1;
                        int h_out = T_rows - h_in - (in_prompt ? 1 : 0);
                        if (my <= h_out) scroll_offset -= 3;
                        else input_scroll_offset -= 3;
                        dirty = 1;
                    }
                }
                consumed += 3 + n_read;
                continue;
            }
        }
        
        int nw = write(mfd, buf + consumed, 1); (void)nw;
        wrote_real_input = 1;
        consumed++;
    }
    
    if (wrote_real_input && !is_altscreen) {
        input_scroll_offset = 0;
        dirty = 1;
    }
}

static void setup_zdotdir(void) {
    snprintf(zdotdir, sizeof zdotdir, "/tmp/.ptysh2-%d", (int)getpid());
    mkdir(zdotdir, 0700);
    char path[512];
    snprintf(path, sizeof path, "%s/.zshenv", zdotdir);
    FILE *f = fopen(path, "w");
    if(f){ fputs("[[ -n \"$PTYSH_HOME\" && -f \"$PTYSH_HOME/.zshenv\" ]] && source \"$PTYSH_HOME/.zshenv\"\n", f); fclose(f); }
    snprintf(path, sizeof path, "%s/.zshrc", zdotdir);
    f = fopen(path, "w");
    if(f){ fputs(
        "[[ -n \"$PTYSH_HOME\" && -f \"$PTYSH_HOME/.zshrc\" ]] && source \"$PTYSH_HOME/.zshrc\"\n\n"
        "autoload -Uz add-zle-hook-widget\n"
        "__ptysh_nav() { printf '\\033_NAV:%d\\033\\\\' \"$HISTNO\"; }\n"
        "add-zle-hook-widget line-pre-redraw __ptysh_nav\n"
        "__ptysh_precmd() { printf '\\033_PS:\\033\\\\' }\n"
        "__ptysh_preexec() { printf '\\033_CS:%d\\033\\\\' \"$HISTCMD\" }\n"
        "precmd_functions+=(__ptysh_precmd)\n"
        "preexec_functions+=(__ptysh_preexec)\n", f); fclose(f); }
}

int main(void) {
    term_size();
    setup_zdotdir();
    
    vt = vterm_new(T_rows, T_cols);
    vterm_set_utf8(vt, 1);
    vts_state = vterm_obtain_state(vt);
    vterm_state_set_bold_highbright(vts_state, 1);
    vts = vterm_obtain_screen(vt);
    vterm_screen_enable_altscreen(vts, 1);
    vterm_screen_set_callbacks(vts, &cb_screen, NULL);
    vterm_screen_reset(vts, 1);
    
    struct winsize ws = { (unsigned short)T_rows, (unsigned short)T_cols, 0, 0 };
    cpid = forkpty(&mfd, NULL, NULL, &ws);
    if (cpid == 0) {
        const char *home = getenv("HOME");
        if (!home) home = "/root";
        setenv("ZDOTDIR", zdotdir, 1);
        setenv("PTYSH_HOME", home, 1);
        setenv("TERM", "xterm-256color", 1);
        execl("/bin/zsh", "zsh", NULL);
        exit(1);
    }
    
    signal(SIGWINCH, handle_winch);
    signal(SIGCHLD,  handle_chld);
    
    term_raw();
    printf("\033[?1000h\033[?1006h");
    printf("\033[2J\033[H");
    dirty = 1;
    
    unsigned char rbuf[32768], kbuf[256];
    for (;;) {
        if (sig_chld) {
            int ws_status;
            if (waitpid(cpid, &ws_status, WNOHANG) == cpid)
                if (WIFEXITED(ws_status) || WIFSIGNALED(ws_status)) break;
            sig_chld = 0;
        }
        if (sig_winch) {
            term_size();
            vterm_set_size(vt, T_rows, T_cols);
            struct winsize win = { (unsigned short)T_rows, (unsigned short)T_cols, 0, 0 };
            ioctl(mfd, TIOCSWINSZ, &win);
            sig_winch = 0; dirty = 1;
        }
        
        fd_set rset; FD_ZERO(&rset);
        FD_SET(STDIN_FILENO, &rset); FD_SET(mfd, &rset);
        struct timeval tv = { 0, 50000 };
        int sel = select(mfd + 1, &rset, NULL, NULL, &tv);
        if (sel < 0) { if (errno == EINTR) continue; break; }
        
        if (FD_ISSET(mfd, &rset)) {
            int nr = read(mfd, rbuf, sizeof rbuf);
            if (nr <= 0) break;
            for (int i = 0; i < nr; i++) proc_pty_byte(rbuf[i]);
        }
        if (FD_ISSET(STDIN_FILENO, &rset)) {
            int nr = read(STDIN_FILENO, kbuf, sizeof kbuf);
            if (nr <= 0) break;
            handle_input(kbuf, nr);
        }
        if (dirty) draw();
    }
    
    printf("\033[?1000l\033[?1006l\033[2J\033[H");
    term_restore();
    return 0;
}
