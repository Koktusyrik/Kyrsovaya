#define _CRT_SECURE_NO_WARNINGS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>

#ifdef __APPLE__
#include <GLUT/glut.h>
#else
#include <GL/glut.h>
#endif

#define WIDTH 800
#define HEIGHT 800

#define MENU_MAIN 0
#define MENU_COLOR 1
#define PLAYING 2
#define GAME_OVER 3

#define MODE_HUMAN_VS_HUMAN 0
#define MODE_HUMAN_VS_BOT   1

#define WHITE_PLAYER 1
#define BLACK_PLAYER -1

#define EMPTY 0
#define WHITE_MAN 1
#define BLACK_MAN -1
#define WHITE_KING 2
#define BLACK_KING -2

#define MAX_MOVES 512
#define INF 1000000

#define BENCH 1

typedef struct {
    int from_r, from_c;
    int to_r, to_c;
    int captured_count;
    int captured[12][2];
} Move;

int game_state = MENU_MAIN;
int game_mode = MODE_HUMAN_VS_HUMAN;
int current_player = WHITE_MAN;
int human_color = WHITE_MAN;

int board[8][8];

long long nodes = 0;

int selected_r = -1, selected_c = -1;
int possible_moves[8][8];

char winner_message[100] = "";

int in_board(int r, int c) {
    return r >= 0 && r < 8 && c >= 0 && c < 8;
}

int is_enemy(int player, int piece) {
    return piece * player < 0;
}

int is_friend(int player, int piece) {
    return piece * player > 0;
}

int is_king(int piece) {
    return piece == WHITE_KING || piece == BLACK_KING;
}

void copy_board(int src[8][8], int dst[8][8]) {
    memcpy(dst, src, sizeof(int) * 64);
}

void init_board() {
    for (int r = 0; r < 8; r++)
        for (int c = 0; c < 8; c++)
            board[r][c] = EMPTY;
    for (int r = 0; r < 3; r++)
        for (int c = 0; c < 8; c++)
            if ((r + c) % 2 == 1)
                board[r][c] = BLACK_MAN;
    for (int r = 5; r < 8; r++)
        for (int c = 0; c < 8; c++)
            if ((r + c) % 2 == 1)
                board[r][c] = WHITE_MAN;
    current_player = WHITE_MAN;
    selected_r = selected_c = -1;
    memset(possible_moves, 0, sizeof(possible_moves));
    winner_message[0] = '\0';
}

#define TT_SIZE (1 << 21)

typedef struct {
    uint64_t key;
    int value;
    short depth;
    char used;
} TTEntry;

static TTEntry tt[TT_SIZE];

void clear_tt(void) {
    memset(tt, 0, sizeof(tt));
}

static void tt_store(TTEntry* e, uint64_t hash, int depth, int value) {
    e->key = hash;
    e->value = value;
    e->depth = (short)depth;
    e->used = 1;
}

static uint64_t zobrist[64][4];
static uint64_t zobrist_side;
static uint64_t rng_state = 88172645463325252ULL;

static uint64_t rand64(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}

void init_zobrist(void) {
    for (int i = 0; i < 64; i++)
        for (int k = 0; k < 4; k++)
            zobrist[i][k] = rand64();
    zobrist_side = rand64();
}

static int piece_index(int p) {
    if (p == WHITE_MAN) return 0;
    if (p == BLACK_MAN) return 1;
    if (p == WHITE_KING) return 2;
    return 3;
}

uint64_t compute_hash(void) {
    uint64_t h = 0;
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            int p = board[r][c];
            if (p != EMPTY)
                h ^= zobrist[r * 8 + c][piece_index(p)];
        }
    }
    if (current_player == BLACK_MAN)
        h ^= zobrist_side;
    return h;
}

void search_captures(int r, int c, int player, Move current,
    Move moves[], int* count, int temp_board[8][8]) {

    int piece = temp_board[r][c];
    int found = 0;

    int dirs[4][2] = { {-1,-1},{-1,1},{1,-1},{1,1} };

    for (int d = 0; d < 4; d++) {
        int dr = dirs[d][0];
        int dc = dirs[d][1];

        if (is_king(piece)) {
            int r1 = r + dr;
            int c1 = c + dc;
            int enemy_r = -1, enemy_c = -1;

            while (in_board(r1, c1)) {
                if (temp_board[r1][c1] != EMPTY) {
                    if (is_enemy(player, temp_board[r1][c1])) {
                        enemy_r = r1;
                        enemy_c = c1;
                        break;
                    }
                    else {
                        break;
                    }
                }
                r1 += dr;
                c1 += dc;
            }

            if (enemy_r != -1) {
                int r2 = enemy_r + dr;
                int c2 = enemy_c + dc;
                while (in_board(r2, c2) && temp_board[r2][c2] == EMPTY) {
                    found = 1;
                    int backup[8][8];
                    copy_board(temp_board, backup);

                    backup[r][c] = EMPTY;
                    backup[enemy_r][enemy_c] = EMPTY;
                    backup[r2][c2] = piece;

                    Move next = current;
                    next.to_r = r2;
                    next.to_c = c2;
                    next.captured[next.captured_count][0] = enemy_r;
                    next.captured[next.captured_count][1] = enemy_c;
                    next.captured_count++;

                    search_captures(r2, c2, player, next, moves, count, backup);

                    r2 += dr;
                    c2 += dc;
                }
            }
        }
        else {
            int r1 = r + dr;
            int c1 = c + dc;
            int r2 = r + 2 * dr;
            int c2 = c + 2 * dc;

            if (in_board(r2, c2) &&
                is_enemy(player, temp_board[r1][c1]) &&
                temp_board[r2][c2] == EMPTY) {

                found = 1;
                int backup[8][8];
                copy_board(temp_board, backup);

                backup[r][c] = EMPTY;
                backup[r1][c1] = EMPTY;
                backup[r2][c2] = piece;

                Move next = current;
                next.to_r = r2;
                next.to_c = c2;
                next.captured[next.captured_count][0] = r1;
                next.captured[next.captured_count][1] = c1;
                next.captured_count++;

                search_captures(r2, c2, player, next, moves, count, backup);
            }
        }
    }

    if (!found && current.captured_count > 0) {
        moves[(*count)++] = current;
    }
}

void generate_moves(int player, Move moves[], int* count) {
    *count = 0;
    Move captures[MAX_MOVES];
    int cap_count = 0;

    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            if (!is_friend(player, board[r][c])) continue;

            Move start = { r, c, r, c, 0 };
            int temp[8][8];
            copy_board(board, temp);
            search_captures(r, c, player, start, captures, &cap_count, temp);
        }
    }

    if (cap_count > 0) {
        memcpy(moves, captures, sizeof(Move) * cap_count);
        *count = cap_count;
        return;
    }

    int dirs[4][2] = { {-1,-1},{-1,1},{1,-1},{1,1} };

    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            int piece = board[r][c];
            if (!is_friend(player, piece)) continue;

            for (int d = 0; d < 4; d++) {
                int dr = dirs[d][0];
                int dc = dirs[d][1];

                if (is_king(piece)) {
                    int nr = r + dr;
                    int nc = c + dc;
                    while (in_board(nr, nc) && board[nr][nc] == EMPTY) {
                        Move m = { r, c, nr, nc, 0 };
                        moves[(*count)++] = m;
                        nr += dr;
                        nc += dc;
                    }
                }
                else {
                    if (player == WHITE_MAN && dr > 0) continue;
                    if (player == BLACK_MAN && dr < 0) continue;
                    int nr = r + dr;
                    int nc = c + dc;
                    if (in_board(nr, nc) && board[nr][nc] == EMPTY) {
                        Move m = { r, c, nr, nc, 0 };
                        moves[(*count)++] = m;
                    }
                }
            }
        }
    }
}

void make_move(Move* m) {
    int piece = board[m->from_r][m->from_c];
    board[m->from_r][m->from_c] = EMPTY;
    board[m->to_r][m->to_c] = piece;

    for (int i = 0; i < m->captured_count; i++) {
        int cr = m->captured[i][0];
        int cc = m->captured[i][1];
        board[cr][cc] = EMPTY;
    }

    if (piece == WHITE_MAN && m->to_r == 0)
        board[m->to_r][m->to_c] = WHITE_KING;
    if (piece == BLACK_MAN && m->to_r == 7)
        board[m->to_r][m->to_c] = BLACK_KING;

    current_player = -current_player;
}

void unmake_move(Move* m, int backup[8][8], int prev_player) {
    copy_board(backup, board);
    current_player = prev_player;
}

int evaluate() {
    int score = 0;
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            int p = board[r][c];
            if (p == EMPTY) continue;

            int val = 0;
            if (p == WHITE_MAN) val = 120 + (7 - r) * 15;
            if (p == BLACK_MAN) val = 120 + r * 15;
            if (p == WHITE_KING) val = 450;
            if (p == BLACK_KING) val = 450;

            if (r >= 2 && r <= 5 && c >= 2 && c <= 5)
                val += 20;

            score += val * (p > 0 ? 1 : -1);
        }
    }
    return score;
}

int minimax(int depth, int alpha, int beta, int maximizing) {
    nodes++;

    int orig_alpha = alpha;
    int orig_beta = beta;
    uint64_t hash = compute_hash();
    TTEntry* e = &tt[hash & (TT_SIZE - 1)];
    if (e->used && e->key == hash && e->depth == depth) {
        return e->value;
    }

    Move moves[MAX_MOVES];
    int count;
    generate_moves(current_player, moves, &count);

    if (depth == 0 || count == 0) {
        int v = evaluate();
        tt_store(e, hash, depth, v);
        return v;
    }

    int result;
    if (maximizing) {
        int max_eval = -INF;
        for (int i = 0; i < count; i++) {
            int backup[8][8];
            copy_board(board, backup);
            int prev = current_player;
            make_move(&moves[i]);
            int eval = minimax(depth - 1, alpha, beta, 0);
            unmake_move(&moves[i], backup, prev);

            if (eval > max_eval) max_eval = eval;
            if (eval > alpha) alpha = eval;
            if (beta <= alpha) break;
        }
        result = max_eval;
    }
    else {
        int min_eval = INF;
        for (int i = 0; i < count; i++) {
            int backup[8][8];
            copy_board(board, backup);
            int prev = current_player;

            make_move(&moves[i]);
            int eval = minimax(depth - 1, alpha, beta, 1);
            unmake_move(&moves[i], backup, prev);

            if (eval < min_eval) min_eval = eval;
            if (eval < beta) beta = eval;
            if (beta <= alpha) break;
        }
        result = min_eval;
    }

    if (result > orig_alpha && result < orig_beta)
        tt_store(e, hash, depth, result);
    return result;
}

void computer_move() {
    Move moves[MAX_MOVES];
    int count;
    generate_moves(current_player, moves, &count);
    if (count == 0) return;

    int best = -INF;
    int best_i = 0;

    for (int depth = 4; depth <= 8; depth++) {
        for (int i = 0; i < count; i++) {
            int backup[8][8];
            copy_board(board, backup);
            int prev = current_player;

            make_move(&moves[i]);
            int val = minimax(depth - 1, -INF, INF, (current_player == WHITE_MAN) ? 1 : 0);
            unmake_move(&moves[i], backup, prev);

            if (val > best) {
                best = val;
                best_i = i;
            }
        }
    }

    make_move(&moves[best_i]);
    glutPostRedisplay();
}

void check_game_over() {
    Move dummy[MAX_MOVES];
    int move_count;
    generate_moves(current_player, dummy, &move_count);
    if (move_count == 0) {
        if (current_player == WHITE_MAN) {
            strcpy(winner_message, "Black wins!");
        }
        else {
            strcpy(winner_message, "White wins!");
        }
        game_state = GAME_OVER;
    }
}

void draw_board() {
    glClear(GL_COLOR_BUFFER_BIT);
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            if ((r + c) % 2 == 0)
                glColor3f(0.9f, 0.9f, 0.8f);
            else
                glColor3f(0.4f, 0.2f, 0.0f);
            float x = c * 0.125f;
            float y = (7 - r) * 0.125f;
            glBegin(GL_QUADS);
            glVertex2f(x, y);
            glVertex2f(x + 0.125f, y);
            glVertex2f(x + 0.125f, y + 0.125f);
            glVertex2f(x, y + 0.125f);
            glEnd();
        }
    }
    if (selected_r >= 0) {
        glColor3f(0.0f, 1.0f, 0.0f);
        float x = selected_c * 0.125f;
        float y = (7 - selected_r) * 0.125f;
        glBegin(GL_LINE_LOOP);
        glVertex2f(x, y);
        glVertex2f(x + 0.125f, y);
        glVertex2f(x + 0.125f, y + 0.125f);
        glVertex2f(x, y + 0.125f);
        glEnd();
    }
    glColor3f(0.0f, 0.0f, 1.0f);
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            if (possible_moves[r][c]) {
                float x = c * 0.125f;
                float y = (7 - r) * 0.125f;
                glBegin(GL_LINE_LOOP);
                glVertex2f(x, y);
                glVertex2f(x + 0.125f, y);
                glVertex2f(x + 0.125f, y + 0.125f);
                glVertex2f(x, y + 0.125f);
                glEnd();
            }
        }
    }
}
void draw_pieces() {
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            int piece = board[r][c];
            if (piece == EMPTY) continue;
            float cx = c * 0.125f + 0.0625f;
            float cy = (7 - r) * 0.125f + 0.0625f;
            float rad = 0.045f;
            if (piece == WHITE_MAN || piece == WHITE_KING)
                glColor3f(1.0f, 1.0f, 1.0f);
            else
                glColor3f(0.1f, 0.1f, 0.1f);
            glBegin(GL_TRIANGLE_FAN);
            glVertex2f(cx, cy);
            for (int k = 0; k <= 20; k++) {
                float angle = 2.0f * 3.14159265f * k / 20.0f;
                glVertex2f(cx + rad * cosf(angle), cy + rad * sinf(angle));
            }
            glEnd();
            if (piece == WHITE_KING || piece == BLACK_KING) {
                glColor3f(1.0f, 0.8f, 0.0f);
                glBegin(GL_TRIANGLES);
                glVertex2f(cx - 0.015f, cy + 0.015f);
                glVertex2f(cx, cy + 0.04f);
                glVertex2f(cx + 0.015f, cy + 0.015f);
                glEnd();
            }
        }
    }
}

void draw_menu_main() {
    glClear(GL_COLOR_BUFFER_BIT);
    glColor3f(1.0f, 1.0f, 1.0f);
    void* font = GLUT_BITMAP_HELVETICA_18;
    const char* line1 = "1. Human vs Human";
    const char* line2 = "2. Human vs Bot";
    const char* line3 = "3. Exit";
    glRasterPos2f(0.3f, 0.6f);
    for (const char* c = line1; *c; c++) glutBitmapCharacter(font, *c);
    glRasterPos2f(0.3f, 0.5f);
    for (const char* c = line2; *c; c++) glutBitmapCharacter(font, *c);
    glRasterPos2f(0.3f, 0.4f);
    for (const char* c = line3; *c; c++) glutBitmapCharacter(font, *c);
    glutSwapBuffers();
}

void draw_menu_color() {
    glClear(GL_COLOR_BUFFER_BIT);
    glColor3f(1.0f, 1.0f, 1.0f);
    void* font = GLUT_BITMAP_HELVETICA_18;
    const char* line1 = "Choose your color:";
    const char* line2 = "1. Play as White (bot plays black)";
    const char* line3 = "2. Play as Black (bot plays white)";
    const char* line4 = "3. Back to main menu";
    glRasterPos2f(0.3f, 0.6f);
    for (const char* c = line1; *c; c++) glutBitmapCharacter(font, *c);
    glRasterPos2f(0.3f, 0.5f);
    for (const char* c = line2; *c; c++) glutBitmapCharacter(font, *c);
    glRasterPos2f(0.3f, 0.4f);
    for (const char* c = line3; *c; c++) glutBitmapCharacter(font, *c);
    glRasterPos2f(0.3f, 0.3f);
    for (const char* c = line4; *c; c++) glutBitmapCharacter(font, *c);
    glutSwapBuffers();
}

void draw_game_over() {
    glClear(GL_COLOR_BUFFER_BIT);
    glColor3f(1.0f, 1.0f, 1.0f);
    void* font = GLUT_BITMAP_HELVETICA_18;

    if (winner_message[0] != '\0') {
        glRasterPos2f(0.35f, 0.6f);
        for (const char* c = winner_message; *c; c++) glutBitmapCharacter(font, *c);
    }

    const char* text = "Press 'r' to restart, 'm' for menu";
    glRasterPos2f(0.2f, 0.5f);
    for (const char* c = text; *c; c++) glutBitmapCharacter(font, *c);
    glutSwapBuffers();
}

void display(void) {
    if (game_state == MENU_MAIN) draw_menu_main();
    else if (game_state == MENU_COLOR) draw_menu_color();
    else if (game_state == PLAYING) {
        draw_board();
        draw_pieces();
        glutSwapBuffers();
    }
    else if (game_state == GAME_OVER) draw_game_over();
}

void reshape(int w, int h) {
    glViewport(0, 0, w, h);
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluOrtho2D(0.0, 1.0, 0.0, 1.0);
    glMatrixMode(GL_MODELVIEW);
}

void mouse(int button, int state, int x, int y) {
    if (game_state != PLAYING || button != GLUT_LEFT_BUTTON || state != GLUT_DOWN)
        return;
    float fx = (float)x / glutGet(GLUT_WINDOW_WIDTH);
    float fy = 1.0f - (float)y / glutGet(GLUT_WINDOW_HEIGHT);
    int col = (int)(fx * 8);
    int row = 7 - (int)(fy * 8);
    if (!in_board(row, col)) return;

    int human_turn = (game_mode == MODE_HUMAN_VS_HUMAN) ||
        (game_mode == MODE_HUMAN_VS_BOT && current_player == human_color);
    if (!human_turn) return;
    if (selected_r == -1) {
        if (is_friend(current_player, board[row][col])) {
            selected_r = row; selected_c = col;
            Move moves[MAX_MOVES];
            int count;
            generate_moves(current_player, moves, &count);
            memset(possible_moves, 0, sizeof(possible_moves));
            for (int i = 0; i < count; i++) {
                if (moves[i].from_r == selected_r && moves[i].from_c == selected_c) {
                    possible_moves[moves[i].to_r][moves[i].to_c] = 1;
                }
            }
        }
    }
    else {
        Move moves[MAX_MOVES];
        int count;
        generate_moves(current_player, moves, &count);
        int moved = 0;
        for (int i = 0; i < count; i++) {
            if (moves[i].from_r == selected_r && moves[i].from_c == selected_c &&
                moves[i].to_r == row && moves[i].to_c == col) {
                make_move(&moves[i]);
                moved = 1;
                break;
            }
        }
        selected_r = selected_c = -1;
        memset(possible_moves, 0, sizeof(possible_moves));
        if (moved) {
            check_game_over();
            if (game_state == PLAYING && game_mode == MODE_HUMAN_VS_BOT && current_player != human_color) {
                computer_move();
                check_game_over();
            }
        }
    }
    glutPostRedisplay();
}

void keyboard(unsigned char key, int x, int y) {
    if (game_state == MENU_MAIN) {
        switch (key) {
        case '1':
            game_mode = MODE_HUMAN_VS_HUMAN;
            init_board();
            game_state = PLAYING;
            break;
        case '2':
            game_state = MENU_COLOR;
            break;
        case '3':
            exit(0);
        }
    }
    else if (game_state == MENU_COLOR) {
        switch (key) {
        case '1':
            game_mode = MODE_HUMAN_VS_BOT;
            human_color = WHITE_MAN;
            init_board();
            game_state = PLAYING;
            break;
        case '2':
            game_mode = MODE_HUMAN_VS_BOT;
            human_color = BLACK_MAN;
            init_board();
            game_state = PLAYING;
            if (current_player != human_color) {
                computer_move();
                check_game_over();
            }
            break;
        case '3':
            game_state = MENU_MAIN;
            break;
        }
    }
    else if (game_state == PLAYING || game_state == GAME_OVER) {
        if (key == 'r') {
            init_board();
            game_state = PLAYING;
            glutPostRedisplay();
        }
        else if (key == 'm') {
            game_state = MENU_MAIN;
            glutPostRedisplay();
        }
    }
    glutPostRedisplay();
}

void bench() {
    for (int d = 4; d <= 12; d++) {
        init_board();
        nodes = 0;
        int best = -INF;
        clock_t t0 = clock();

        Move moves[MAX_MOVES];
        int count;
        generate_moves(current_player, moves, &count);
        for (int i = 0; i < count; i++) {
            int backup[8][8];
            copy_board(board, backup);
            int prev = current_player;
            make_move(&moves[i]);
            int v = minimax(d - 1, -INF, INF, (current_player == WHITE_MAN) ? 1 : 0);
            if (v > best) best = v;
            unmake_move(&moves[i], backup, prev);
        }
        double sec = (double)(clock() - t0) / CLOCKS_PER_SEC;
        printf("depth %d: %.3f s, nodes %lld, best %d\n", d, sec, nodes, best);
        fflush(stdout);
    }
}

int main(int argc, char** argv) {
    init_zobrist();
#if BENCH
    bench();
    printf("Done. Press Enter...\n");
    getchar();
    return 0;
#endif
    glutInit(&argc, argv);
    glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGB);
    glutInitWindowSize(WIDTH, HEIGHT);
    glutCreateWindow("Checkers");
    glClearColor(0.2f, 0.2f, 0.2f, 1.0f);
    glutDisplayFunc(display);
    glutReshapeFunc(reshape);
    glutMouseFunc(mouse);
    glutKeyboardFunc(keyboard);
    init_board();
    glutMainLoop();
    return 0;
}
