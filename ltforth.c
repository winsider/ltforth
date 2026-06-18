#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <arm/limits.h>

/* CONSTANTS */
#define VERSION "0.1.0"
#define LINE_SIZE 128
#define TRUE 1
#define FALSE 0
#define DATA_STACK_SIZE 64
#define WORD_FLAG_IMMEDIATE 0x01
#define FORTH_TRUE  ((cell_t)-1)
#define FORTH_FALSE ((cell_t)0)
#define DICTIONARY_WORDS 64
#define DICTIONARY_NAME_BYTES 512
#define INSTRUCTION_SPACE_SIZE 512

/* TYPES */
typedef struct
{
    const char* start;
    size_t length;
} Text;

typedef Text Token;
typedef int (*word_fun_t)(void);

typedef struct Word Word;

typedef enum
{
    WORD_BUILTIN,
    WORD_COLON
} word_kind_t;

typedef int (*word_func_t)(void);

typedef int cell_t;
typedef unsigned ucell_t;
typedef unsigned char byte_t;
typedef size_t idx_t;
typedef unsigned char flags_t;

typedef enum
{
    OP_CALL,
    OP_LIT
} opcode_t;

typedef struct
{
    opcode_t op;

    union
    {
        Word* word;
        cell_t literal;
    } arg;
} Instruction;

struct Word
{
    Token name;
    flags_t flags;
    word_kind_t kind;

    union
    {
        word_func_t builtin;

        struct
        {
            Instruction* first;
            idx_t length;
        } colon;
    } impl;
};

typedef enum
{
    STATE_INTERPRET,
    STATE_COMPILE
} forth_state_t;

static forth_state_t state = STATE_INTERPRET;
static Word* current_definition = NULL;

/* GLOBALS */
static char input_buffer[LINE_SIZE];
static idx_t tokeniser_pos = 0;

static cell_t data_stack[DATA_STACK_SIZE];
static idx_t dsp = 0;

static Word dictionary_words[DICTIONARY_WORDS];
static idx_t dictionary_word_count = 0;

static char dictionary_names[DICTIONARY_NAME_BYTES];
static idx_t dictionary_name_pos = 0;

static Instruction instruction_space[INSTRUCTION_SPACE_SIZE];
static idx_t instruction_count = 0;

/* MACRO FUNCTIONS */
#define has_more_input() (input_buffer[tokeniser_pos]!='\0')
#define TEXT_LITERAL(s) ((Token){ (s), sizeof(s) - 1 })
#define PUSH_UNCHECKED(v) (data_stack[dsp++] = (v))
#define POP_UNCHECKED(v)  ((v) = data_stack[--dsp])
#define REQUIRE_STACK(n)                     \
    {                                        \
        if (dsp < (n))                       \
        {                                    \
            error("data stack underflow");   \
            return FALSE;                    \
        }                                    \
    }
#define REQUIRE_SPACE(n)                                       \
    do                                                         \
    {                                                          \
        if ((DATA_STACK_SIZE - dsp) < (idx_t)(n))              \
        {                                                      \
            error("data stack overflow");                      \
            return FALSE;                                      \
        }                                                      \
    } while (0)

/* FUNCTIONS */
static void error(const char* msg)
{
    fprintf(stderr, "ERROR: %s\n", msg);
    fflush(stderr);
}

static int push(cell_t value)
{
    if (dsp >= DATA_STACK_SIZE)
    {
        error("data stack overflow");
        return FALSE;
    }
    data_stack[dsp++] = value;
    return TRUE;
}

static int pop(cell_t* value)
{
    REQUIRE_STACK(1);
    POP_UNCHECKED(*value);
    return TRUE;
}

static Instruction* allot_instruction(void)
{
    if (instruction_count >= INSTRUCTION_SPACE_SIZE)
    {
        return NULL;
    }

    return &instruction_space[instruction_count++];
}

static Word* allot_word(void)
{
    if (dictionary_word_count >= DICTIONARY_WORDS)
    {
        return NULL;
    }

    return &dictionary_words[dictionary_word_count++];
}

static int copy_name(Token* dest, const Token* src)
{
    if (dictionary_name_pos + src->length > DICTIONARY_NAME_BYTES)
    {
        return FALSE;
    }

    dest->start = &dictionary_names[dictionary_name_pos];
    dest->length = src->length;

    memcpy(&dictionary_names[dictionary_name_pos], src->start, src->length);
    dictionary_name_pos += src->length;

    return TRUE;
}

static int text_equal(const Text* t1, const Text* t2)
{
    return ((t1->length == t2->length) &&
            (strncmp(t1->start, t2->start, t1->length) == 0));
}

static Word* find_word(const Token* token)
{
    idx_t i;

    for (i = dictionary_word_count; i > 0; --i)
    {
        Word* word = &dictionary_words[i - 1];

        if (text_equal(&word->name, token))
        {
            return word;
        }
    }

    return NULL;
}

static int parse_number(const Token* token, cell_t* value)
{
    idx_t i = 0;
    int negative = FALSE;
    ucell_t result = 0;

    if (token->length == 0)
    {
        return FALSE;
    }

    if (token->start[i] == '-')
    {
        negative = TRUE;
        ++i;
    }
    else if (token->start[i] == '+')
    {
        ++i;
    }

    if (i == token->length)
    {
        return FALSE;
    }

    while (i < token->length)
    {
        unsigned char c = (unsigned char)token->start[i];

        if (!isdigit(c))
        {
            return FALSE;
        }

        result = (ucell_t)(result * 10u + (ucell_t)(c - '0'));
        ++i;
    }

    if (negative)
    {
        *value = (cell_t)(0u - result);
    }
    else
    {
        *value = (cell_t)result;
    }

    return TRUE;
}

static void skip_ignored()
{
    for (;;)
    {
        // skip whitespace
        while (isspace((unsigned char)input_buffer[tokeniser_pos]))
        {
            ++tokeniser_pos;
        }

        // skip comment
        if (input_buffer[tokeniser_pos] == '\\')
        {
            do
            {
                tokeniser_pos++;
            } while (input_buffer[tokeniser_pos] != '\n' &&
                     input_buffer[tokeniser_pos] != '\0');
            continue;
        }
        break;
    }
}

static int compile_word(Word* word)
{
    Instruction* instruction;

    if (current_definition == NULL)
    {
        error("no current definition");
        return FALSE;
    }

    instruction = allot_instruction();
    if (instruction == NULL)
    {
        error("instruction space full");
        return FALSE;
    }

    if (current_definition->impl.colon.length == 0)
    {
        current_definition->impl.colon.first = instruction;
    }

    instruction->op = OP_CALL;
    instruction->arg.word = word;

    ++current_definition->impl.colon.length;

    return TRUE;
}

static int compile_literal(cell_t value)
{
    Instruction* instruction;

    if (current_definition == NULL)
    {
        error("no current definition");
        return FALSE;
    }

    instruction = allot_instruction();
    if (instruction == NULL)
    {
        error("instruction space full");
        return FALSE;
    }

    if (current_definition->impl.colon.length == 0)
    {
        current_definition->impl.colon.first = instruction;
    }

    instruction->op = OP_LIT;
    instruction->arg.literal = value;

    ++current_definition->impl.colon.length;

    return TRUE;
}

static int execute_colon_word(Word* word);

static int execute_word(Word* word)
{
    if (word->kind == WORD_BUILTIN)
    {
        return word->impl.builtin();
    }

    if (word->kind == WORD_COLON)
    {
        return execute_colon_word(word);
    }

    error("invalid word kind");
    return FALSE;
}

static int execute_colon_word(Word* word)
{
    idx_t i;
    Instruction* instruction;

    for (i = 0; i < word->impl.colon.length; ++i)
    {
        instruction = &word->impl.colon.first[i];

        switch (instruction->op)
        {
            case OP_CALL:
                if (!execute_word(instruction->arg.word))
                {
                    return FALSE;
                }
                break;

            case OP_LIT:
                if (!push(instruction->arg.literal))
                {
                    return FALSE;
                }
                break;

            default:
                error("invalid instruction");
                return FALSE;
        }
    }

    return TRUE;
}

static int process_token(const Token* token)
{
    Word* word;
    cell_t value;

    word = find_word(token);

    if (state == STATE_INTERPRET)
    {
        if (word != NULL)
        {
            return execute_word(word);
        }

        if (parse_number(token, &value))
        {
            return push(value);
        }

        error("unknown word");
        return FALSE;
    }

    /* STATE_COMPILE */

    if (word != NULL)
    {
        if (word->flags & WORD_FLAG_IMMEDIATE)
        {
            return execute_word(word);
        }

        return compile_word(word);
    }

    if (parse_number(token, &value))
    {
        return compile_literal(value);
    }

    error("unknown word while compiling");
    return FALSE;
}

static int next_token(Token* out)
{
    skip_ignored();
    if (!has_more_input())
    {
        return FALSE;
    }

    out->start = input_buffer + tokeniser_pos;
    out->length = 0;

    do
    {
        tokeniser_pos++;
        out->length++;
    } while (!isspace((unsigned char)input_buffer[tokeniser_pos]) && has_more_input());

    return TRUE;
}

static int word_add(void)
{
    REQUIRE_STACK(2);
    data_stack[dsp - 2] =
        (cell_t)((ucell_t)data_stack[dsp - 2] +
                 (ucell_t)data_stack[dsp - 1]);
    --dsp;
    return TRUE;
}

static int word_sub(void)
{
    REQUIRE_STACK(2);
    data_stack[dsp - 2] =
        (cell_t)((ucell_t)data_stack[dsp - 2] -
                 (ucell_t)data_stack[dsp - 1]);
    --dsp;
    return TRUE;
}

static int word_mul(void)
{
    REQUIRE_STACK(2);
    data_stack[dsp - 2] =
        (cell_t)((ucell_t)data_stack[dsp - 2] *
                 (ucell_t)data_stack[dsp - 1]);
    --dsp;
    return TRUE;
}

static int word_div(void)
{
    REQUIRE_STACK(2);
    if (data_stack[dsp - 1] == 0)
    {
        error("division by zero");
        return FALSE;
    }
    data_stack[dsp - 2] =
        data_stack[dsp - 2] / data_stack[dsp - 1];

    --dsp;
    return TRUE;
}

static int word_dot(void)
{
    cell_t value;
    REQUIRE_STACK(1);
    POP_UNCHECKED(value);
    printf("%d ", value);
    return TRUE;
}

static int word_dup(void)
{
    REQUIRE_STACK(1);
    REQUIRE_SPACE(1);
    data_stack[dsp] = data_stack[dsp - 1];
    ++dsp;
    return TRUE;
}

static int word_drop(void)
{
    REQUIRE_STACK(1);
    --dsp;
    return TRUE;
}

static int word_swap(void)
{
    cell_t tmp;
    REQUIRE_STACK(2);
    tmp = data_stack[dsp - 1];
    data_stack[dsp - 1] = data_stack[dsp - 2];
    data_stack[dsp - 2] = tmp;
    return TRUE;
}

static int word_over(void)
{
    REQUIRE_STACK(2);
    REQUIRE_SPACE(1);
    data_stack[dsp] = data_stack[dsp - 2];
    ++dsp;
    return TRUE;
}

static int word_rot(void)
{
    cell_t tmp;
    REQUIRE_STACK(3);
    tmp = data_stack[dsp - 3];
    data_stack[dsp - 3] = data_stack[dsp - 2];
    data_stack[dsp - 2] = data_stack[dsp - 1];
    data_stack[dsp - 1] = tmp;
    return TRUE;
}

static int word_dots(void)
{
    idx_t i;
    printf("<%u> ", (unsigned)dsp);
    for (i = 0; i < dsp; ++i)
    {
        printf("%d ", data_stack[i]);
    }
    return TRUE;
}

static int word_eq(void)
{
    REQUIRE_STACK(2);
    data_stack[dsp - 2] =
        (data_stack[dsp - 2] == data_stack[dsp - 1])
            ? FORTH_TRUE
            : FORTH_FALSE;
    --dsp;
    return TRUE;
}

static int word_lt(void)
{
    REQUIRE_STACK(2);
    data_stack[dsp - 2] =
        (data_stack[dsp - 2] < data_stack[dsp - 1])
            ? FORTH_TRUE
            : FORTH_FALSE;
    --dsp;
    return TRUE;
}

static int word_gt(void)
{
    REQUIRE_STACK(2);
    data_stack[dsp - 2] =
        (data_stack[dsp - 2] > data_stack[dsp - 1])
            ? FORTH_TRUE
            : FORTH_FALSE;
    --dsp;
    return TRUE;
}

static int word_emit(void)
{
    REQUIRE_STACK(1);
    putchar((unsigned char)data_stack[dsp - 1]);
    --dsp;
    return TRUE;
}

static int word_cr(void)
{
    putchar('\n');
    return TRUE;
}

static int word_dep(void)
{
    REQUIRE_SPACE(1);
    data_stack[dsp] = (cell_t)dsp;
    ++dsp;
    return TRUE;
}

static int word_ze(void)
{
    REQUIRE_STACK(1);
    data_stack[dsp - 1] =
        (data_stack[dsp - 1] == 0)
            ? FORTH_TRUE
            : FORTH_FALSE;
    return TRUE;
}

static int word_colon(void)
{
    Token name;
    Word* word;

    if (!next_token(&name))
    {
        error("expected name after ':'");
        return FALSE;
    }

    word = allot_word();
    if (word == NULL)
    {
        error("dictionary full");
        return FALSE;
    }

    if (!copy_name(&word->name, &name))
    {
        error("dictionary name space full");
        return FALSE;
    }

    word->flags = 0;
    word->kind = WORD_COLON;
    word->impl.colon.first = NULL;
    word->impl.colon.length = 0;

    current_definition = word;
    state = STATE_COMPILE;

    return TRUE;
}

static int word_semicolon(void)
{
    if (state != STATE_COMPILE || current_definition == NULL)
    {
        error("';' outside definition");
        return FALSE;
    }

    state = STATE_INTERPRET;
    current_definition = NULL;

    return TRUE;
}

static int add_builtin(Token name,
                       word_func_t function,
                       flags_t flags)
{
    Word* word;

    word = allot_word();
    if (word == NULL)
    {
        error("dictionary full");
        return FALSE;
    }

    word->name = name;
    word->flags = flags;
    word->kind = WORD_BUILTIN;
    word->impl.builtin = function;

    return TRUE;
}

static Word word_add_       = { TEXT_LITERAL("+"),     0, WORD_BUILTIN, NULL, word_add };
static Word word_sub_       = { TEXT_LITERAL("-"),     0, WORD_BUILTIN, NULL,  word_sub };
static Word word_mul_       = { TEXT_LITERAL("*"),     0, WORD_BUILTIN, NULL, word_mul };
static Word word_div_       = { TEXT_LITERAL("/"),     0, WORD_BUILTIN, NULL, word_div };
static Word word_dot_       = { TEXT_LITERAL("."),     0, WORD_BUILTIN, NULL, word_dot };
static Word word_dup_       = { TEXT_LITERAL("dup"),   0, WORD_BUILTIN, NULL, word_dup };
static Word word_drop_      = { TEXT_LITERAL("drop"),  0, WORD_BUILTIN, NULL, word_drop };
static Word word_ze_        = { TEXT_LITERAL("0="),    0, WORD_BUILTIN, NULL, word_ze };
static Word word_dep_       = { TEXT_LITERAL("depth"), 0, WORD_BUILTIN, NULL, word_dep };
static Word word_cr_        = { TEXT_LITERAL("cr"),    0, WORD_BUILTIN, NULL, word_cr };
static Word word_emit_      = { TEXT_LITERAL("emit"),  0, WORD_BUILTIN, NULL, word_emit };
static Word word_swap_      = { TEXT_LITERAL("swap"),  0, WORD_BUILTIN, NULL, word_swap };
static Word word_over_      = { TEXT_LITERAL("over"),  0, WORD_BUILTIN, NULL, word_over };
static Word word_rot_       = { TEXT_LITERAL("rot"),   0, WORD_BUILTIN, NULL, word_rot };
static Word word_dots_      = { TEXT_LITERAL(".s"),    0, WORD_BUILTIN, NULL, word_dots };
static Word word_eq_        = { TEXT_LITERAL("="),     0, WORD_BUILTIN, NULL, word_eq };
static Word word_lt_        = { TEXT_LITERAL("<"),     0, WORD_BUILTIN, NULL, word_lt };
static Word word_gt_        = { TEXT_LITERAL(">"),     0, WORD_BUILTIN, NULL, word_gt };
static Word word_colon_     = { TEXT_LITERAL(":"),     0, WORD_BUILTIN, NULL, word_colon };
static Word word_semicolon_ = { TEXT_LITERAL(";"), WORD_FLAG_IMMEDIATE, WORD_BUILTIN, NULL, word_semicolon };

static void init_dictionary(void)
{
    add_builtin(TEXT_LITERAL("+"), word_add, 0);
    add_builtin(TEXT_LITERAL("-"), word_sub, 0);
    add_builtin(TEXT_LITERAL("*"), word_mul, 0);
    add_builtin(TEXT_LITERAL("/"), word_div, 0);
    add_builtin(TEXT_LITERAL("."), word_dot, 0);
    add_builtin(TEXT_LITERAL("dup"), word_dup, 0);
    add_builtin(TEXT_LITERAL("drop"), word_drop, 0);
    add_builtin(TEXT_LITERAL("0="), word_ze, 0);
    add_builtin(TEXT_LITERAL("depth"), word_dep, 0);
    add_builtin(TEXT_LITERAL("cr"), word_cr, 0);;
    add_builtin(TEXT_LITERAL("emit"), word_emit, 0);;
    add_builtin(TEXT_LITERAL("swap"), word_swap, 0);
    add_builtin(TEXT_LITERAL("over"), word_over, 0);
    add_builtin(TEXT_LITERAL("rot"), word_rot, 0);;
    add_builtin(TEXT_LITERAL(".s"), word_dots, 0);;
    add_builtin(TEXT_LITERAL("="), word_eq, 0);
    add_builtin(TEXT_LITERAL("<"), word_lt, 0);
    add_builtin(TEXT_LITERAL(">"), word_gt, 0);
    add_builtin(TEXT_LITERAL(":"), word_colon, 0);
    add_builtin(TEXT_LITERAL(";"), word_semicolon, 9);
}

int main(void)
{
    printf("ltforth %s\n", VERSION);

    init_dictionary();

    for (;;)
    {
        printf("> ");
        fflush(stdout);
        if (fgets(input_buffer, LINE_SIZE, stdin) == NULL)
        {
            /* end of file or input */
            break;
        }
        tokeniser_pos = 0;
        Token token;
        while (next_token(&token))
        {
            if (!process_token(&token))
            {
                break;
            }
        }
        printf("OK\n");
    }
    return 0;
}
