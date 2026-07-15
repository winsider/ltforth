#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <arm/limits.h>

/* CONSTANTS */
#define VERSION "0.2.0"
#define LINE_SIZE 128
#define TRUE 1
#define FALSE 0
#define DATA_STACK_SIZE 64
#define CONTROL_STACK_SIZE 16
#define RETURN_STACK_SIZE 32
#define FORTH_TRUE  ((cell_t)-1)
#define FORTH_FALSE ((cell_t)0)
#define DICTIONARY_WORDS 64
#define DICTIONARY_NAME_BYTES 512
#define INSTRUCTION_SPACE_SIZE 512
#define WORDS_PER_LINE 4

#define WORD_FLAG_IMMEDIATE  0x01

#define WORD_TYPE_MASK       0xf0
#define WORD_TYPE_BUILTIN    0x10
#define WORD_TYPE_COLON      0x20

#if defined(__unix__) || defined(__APPLE__)
#include <unistd.h>
#define STDIN_IS_INTERACTIVE() isatty(0)
#else
#define STDIN_IS_INTERACTIVE() TRUE
#endif

/* TYPES */
typedef struct
{
    const char* start;
    size_t length;
} Text;

typedef Text Token;
typedef int (*word_fun_t)(void);

typedef struct Word Word;

typedef int (*word_func_t)(void);

typedef int cell_t;
typedef unsigned ucell_t;
typedef unsigned char byte_t;
typedef size_t idx_t;
typedef unsigned char word_flags_t;

typedef enum
{
    OP_CALL,
    OP_LIT,
    OP_BRANCH,
    OP_BRANCH_IF_ZERO,
    OP_DO,
    OP_LOOP,
    OP_I,
    OP_J,
    OP_PLUS_LOOP
} opcode_t;

typedef enum
{
    CONTROL_IF,
    CONTROL_ELSE,
    CONTROL_BEGIN,
    CONTROL_WHILE,
    CONTROL_DO
} control_type_t;

typedef struct
{
    opcode_t op;

    union
    {
        Word* word;
        cell_t literal;
        idx_t branch_target;
    } arg;
} Instruction;

typedef struct
{
    control_type_t type;
    idx_t target;
    Instruction* branch_instruction;
} ControlEntry;

struct Word
{
    Token name;
    word_flags_t flags;

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

typedef struct
{
    idx_t word_count;
    idx_t name_pos;
    idx_t instruction_count;
} dictionary_mark_t;

/* GLOBALS */
static char input_buffer[LINE_SIZE];
static idx_t tokeniser_pos = 0;

static cell_t data_stack[DATA_STACK_SIZE];
static idx_t dsp = 0;

static ControlEntry control_stack[CONTROL_STACK_SIZE];
static idx_t csp = 0;

static cell_t return_stack[RETURN_STACK_SIZE];
static idx_t rsp = 0;

static Word dictionary_words[DICTIONARY_WORDS];
static idx_t dictionary_word_count = 0;

static char dictionary_names[DICTIONARY_NAME_BYTES];
static idx_t dictionary_name_pos = 0;

static Instruction instruction_space[INSTRUCTION_SPACE_SIZE];
static idx_t instruction_count = 0;

static dictionary_mark_t definition_mark;

static forth_state_t state = STATE_INTERPRET;
static Word* current_definition = NULL;

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

#define RPUSH_UNCHECKED(v) (return_stack[rsp++] = (v))
#define RPOP_UNCHECKED(v)  ((v) = return_stack[--rsp])

/* FUNCTIONS */

static void error(const char* msg)
{
    fprintf(stderr, "ERROR: %s\n", msg);
    fflush(stderr);
}

static idx_t current_instruction_index(void)
{
    if (current_definition == NULL)
    {
        return 0;
    }

    return current_definition->impl.colon.length;
}

static void restore_dictionary_mark(const dictionary_mark_t* mark)
{
    dictionary_word_count = mark->word_count;
    dictionary_name_pos = mark->name_pos;
    instruction_count = mark->instruction_count;
}

static void abort_definition(void)
{
    if (state != STATE_COMPILE)
    {
        return;
    }

    restore_dictionary_mark(&definition_mark);

    current_definition = NULL;
    state = STATE_INTERPRET;
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

static int rpush(cell_t value)
{
    if (rsp >= RETURN_STACK_SIZE)
    {
        error("return stack overflow");
        return FALSE;
    }

    return_stack[rsp++] = value;
    return TRUE;
}

static int rpop(cell_t* value)
{
    if (rsp == 0)
    {
        error("return stack underflow");
        return FALSE;
    }

    *value = return_stack[--rsp];
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

static int push_control(control_type_t type,
                        Instruction* branch_instruction,
                        idx_t target)
{
    if (csp >= CONTROL_STACK_SIZE)
    {
        error("control stack overflow");
        return FALSE;
    }

    control_stack[csp].type = type;
    control_stack[csp].branch_instruction = branch_instruction;
    control_stack[csp].target = target;
    ++csp;

    return TRUE;
}

static ControlEntry* top_control(void)
{
    if (csp == 0)
    {
        return NULL;
    }

    return &control_stack[csp - 1];
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

static void print_text(const Text* text)
{
    printf("%.*s", (int)text->length, text->start);
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

static Instruction* compile_instruction(opcode_t op)
{
    Instruction* instruction;

    if (current_definition == NULL)
    {
        error("no current definition");
        return NULL;
    }

    instruction = allot_instruction();
    if (instruction == NULL)
    {
        error("instruction space full");
        return NULL;
    }

    if (current_definition->impl.colon.length == 0)
    {
        current_definition->impl.colon.first = instruction;
    }

    instruction->op = op;
    ++current_definition->impl.colon.length;

    return instruction;
}

static int compile_word(Word* word)
{
    Instruction* instruction;

    instruction = compile_instruction(OP_CALL);
    if (instruction == NULL)
    {
        return FALSE;
    }

    instruction->arg.word = word;
    return TRUE;
}

static int compile_literal(cell_t value)
{
    Instruction* instruction;

    instruction = compile_instruction(OP_LIT);
    if (instruction == NULL)
    {
        return FALSE;
    }

    instruction->arg.literal = value;
    return TRUE;
}

static Instruction* compile_branch(opcode_t op)
{
    Instruction* instruction;

    instruction = compile_instruction(op);
    if (instruction == NULL)
    {
        return NULL;
    }

    instruction->arg.branch_target = 0;
    return instruction;
}

static int word_is_builtin(const Word* word)
{
    return (word->flags & WORD_TYPE_MASK) == WORD_TYPE_BUILTIN;
}

static int word_is_colon(const Word* word)
{
    return (word->flags & WORD_TYPE_MASK) == WORD_TYPE_COLON;
}

static int execute_colon_word(Word* word);

static int execute_word(Word* word)
{
    if (word_is_builtin(word))
    {
        return word->impl.builtin();
    }

    if (word_is_colon(word))
    {
        return execute_colon_word(word);
    }

    error("invalid word type");
    return FALSE;
}

static int execute_colon_word(Word* word)
{
    idx_t ip;
    Instruction* instruction;
    cell_t flag;

    ip = 0;

    while (ip < word->impl.colon.length)
    {
        instruction = &word->impl.colon.first[ip++];

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

            case OP_BRANCH:
                if (instruction->arg.branch_target >
                    word->impl.colon.length)
                {
                    error("invalid branch target");
                    return FALSE;
                }

                ip = instruction->arg.branch_target;
                break;

            case OP_BRANCH_IF_ZERO:
                REQUIRE_STACK(1);

                flag = data_stack[--dsp];

                if (flag == 0)
                {
                    if (instruction->arg.branch_target >
                        word->impl.colon.length)
                    {
                        error("invalid branch target");
                        return FALSE;
                    }

                    ip = instruction->arg.branch_target;
                }
                break;

            case OP_DO:
            {
                cell_t start;
                cell_t limit;

                REQUIRE_STACK(2);

                start = data_stack[--dsp];
                limit = data_stack[--dsp];

                if (start == limit)
                {
                    ip = instruction->arg.branch_target;
                    break;
                }

                if ((RETURN_STACK_SIZE - rsp) < 2)
                {
                    error("return stack overflow");
                    return FALSE;
                }

                return_stack[rsp++] = limit;
                return_stack[rsp++] = start;

                break;
            }

            case OP_I:
            {
                if (rsp < 2)
                {
                    error("return stack underflow");
                    return FALSE;
                }

                if (!push(return_stack[rsp - 1]))
                {
                    return FALSE;
                }

                break;
            }

            case OP_LOOP:
            {
                cell_t index;
                cell_t limit;

                if (rsp < 2)
                {
                    error("return stack underflow");
                    return FALSE;
                }

                index = return_stack[rsp - 1] + 1;
                limit = return_stack[rsp - 2];

                if (index == limit)
                {
                    rsp -= 2;
                }
                else
                {
                    return_stack[rsp - 1] = index;
                    ip = instruction->arg.branch_target;
                }

                break;
            }

            case OP_J:
            {
                if (rsp < 4)
                {
                    error("return stack underflow");
                    return FALSE;
                }

                if (!push(return_stack[rsp - 3]))
                {
                    return FALSE;
                }

                break;
            }

            case OP_PLUS_LOOP:
            {
                cell_t increment;
                cell_t index;
                cell_t limit;
                cell_t next;

                REQUIRE_STACK(1);

                if (rsp < 2)
                {
                    error("return stack underflow");
                    return FALSE;
                }

                increment = data_stack[--dsp];

                if (increment <= 0)
                {
                    error("+loop only supports positive increments");
                    return FALSE;
                }

                index = return_stack[rsp - 1];
                limit = return_stack[rsp - 2];

                next = index + increment;

                if (next >= limit)
                {
                    rsp -= 2;
                }
                else
                {
                    return_stack[rsp - 1] = next;
                    ip = instruction->arg.branch_target;
                }

                break;
            }

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

    if (state != STATE_INTERPRET)
    {
        error("nested definition");
        return FALSE;
    }

    if (!next_token(&name))
    {
        error("expected name after ':'");
        return FALSE;
    }

    definition_mark.word_count = dictionary_word_count;
    definition_mark.name_pos = dictionary_name_pos;
    definition_mark.instruction_count = instruction_count;

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

    word->flags = WORD_TYPE_COLON;
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

    if (csp != 0)
    {
        error("unclosed control structure");
        return FALSE;
    }

    state = STATE_INTERPRET;
    current_definition = NULL;

    return TRUE;
}

static int word_words(void)
{
    idx_t i;

    for (i = 0; i < dictionary_word_count; ++i)
    {
        Word* word = &dictionary_words[i];

        print_text(&word->name);
        putchar(' ');

        if ((i % WORDS_PER_LINE) == (WORDS_PER_LINE - 1))
        {
            putchar('\n');
        }
    }

    if ((dictionary_word_count % WORDS_PER_LINE) != 0)
    {
        putchar('\n');
    }

    return TRUE;
}

static int word_see(void)
{
    Token name;
    Word* word;
    idx_t i;

    if (!next_token(&name))
    {
        error("expected word name after 'see'");
        return FALSE;
    }

    word = find_word(&name);
    if (word == NULL)
    {
        error("unknown word");
        return FALSE;
    }

    if (word_is_builtin(word))
    {
        print_text(&word->name);
        printf(" is builtin\n");
        return TRUE;
    }

    if (!word_is_colon(word))
    {
        error("invalid word type");
        return FALSE;
    }

    printf(": ");
    print_text(&word->name);
    putchar('\n');

    for (i = 0; i < word->impl.colon.length; ++i)
    {
        Instruction* instruction;

        instruction = &word->impl.colon.first[i];

        printf("  %u: ", (unsigned)i);

        switch (instruction->op)
        {
            case OP_CALL:
                print_text(&instruction->arg.word->name);
                break;

            case OP_LIT:
                printf("%d", instruction->arg.literal);
                break;

            case OP_BRANCH:
                printf("branch %u",
                       (unsigned)instruction->arg.branch_target);
                break;

            case OP_BRANCH_IF_ZERO:
                printf("0branch %u",
                       (unsigned)instruction->arg.branch_target);
                break;

            case OP_DO:
                printf("do %u",
                       (unsigned)instruction->arg.branch_target);
                break;

            case OP_LOOP:
                printf("loop %u",
                       (unsigned)instruction->arg.branch_target);
                break;

            case OP_I:
                printf("i");
                break;

            case OP_J:
                printf("j");
                break;

            case OP_PLUS_LOOP:
                printf("+loop %u", (unsigned)instruction->arg.branch_target);
                break;

            default:
                printf("<invalid instruction>");
                break;
        }

        putchar('\n');
    }

    printf(";\n");

    return TRUE;
}

static int word_if(void)
{
    Instruction* branch;

    if (state != STATE_COMPILE)
    {
        error("IF is compile-only");
        return FALSE;
    }

    branch = compile_branch(OP_BRANCH_IF_ZERO);
    if (branch == NULL)
    {
        return FALSE;
    }

    return push_control(CONTROL_IF, branch, 0);
}

static int word_else(void)
{
    ControlEntry* control;
    Instruction* branch;

    if (state != STATE_COMPILE)
    {
        error("ELSE is compile-only");
        return FALSE;
    }

    control = top_control();

    if (control == NULL || control->type != CONTROL_IF)
    {
        error("ELSE without IF");
        return FALSE;
    }

    branch = compile_branch(OP_BRANCH);
    if (branch == NULL)
    {
        return FALSE;
    }

    /*
     * compile_branch() has now added the unconditional branch.
     * The next instruction is the first instruction in the ELSE part.
     */
    control->branch_instruction->arg.branch_target =
        current_definition->impl.colon.length;

    control->type = CONTROL_ELSE;
    control->branch_instruction = branch;

    return TRUE;
}

static int word_then(void)
{
    ControlEntry* control;

    if (state != STATE_COMPILE)
    {
        error("THEN is compile-only");
        return FALSE;
    }

    control = top_control();

    if (control == NULL ||
       (control->type != CONTROL_IF && control->type != CONTROL_ELSE))
    {
        error("THEN without IF");
        return FALSE;
    }

    control->branch_instruction->arg.branch_target =
        current_definition->impl.colon.length;

    --csp;

    return TRUE;
}

static int word_begin(void)
{
    if (state != STATE_COMPILE)
    {
        error("BEGIN is compile-only");
        return FALSE;
    }

    return push_control(CONTROL_BEGIN, NULL, current_instruction_index());
}

static int word_until(void)
{
    ControlEntry* control;
    Instruction* branch;

    if (state != STATE_COMPILE)
    {
        error("UNTIL is compile-only");
        return FALSE;
    }

    control = top_control();

    if (control == NULL || control->type != CONTROL_BEGIN)
    {
        error("UNTIL without BEGIN");
        return FALSE;
    }

    branch = compile_branch(OP_BRANCH_IF_ZERO);
    if (branch == NULL)
    {
        return FALSE;
    }

    branch->arg.branch_target = control->target;

    --csp;

    return TRUE;
}

static int word_while(void)
{
    ControlEntry* control;
    Instruction* branch;
    idx_t begin_target;

    if (state != STATE_COMPILE)
    {
        error("WHILE is compile-only");
        return FALSE;
    }

    control = top_control();

    if (control == NULL || control->type != CONTROL_BEGIN)
    {
        error("WHILE without BEGIN");
        return FALSE;
    }

    begin_target = control->target;

    branch = compile_branch(OP_BRANCH_IF_ZERO);
    if (branch == NULL)
    {
        return FALSE;
    }

    control->type = CONTROL_WHILE;
    control->target = begin_target;
    control->branch_instruction = branch;

    return TRUE;
}

static int word_repeat(void)
{
    ControlEntry* control;
    Instruction* branch;

    if (state != STATE_COMPILE)
    {
        error("REPEAT is compile-only");
        return FALSE;
    }

    control = top_control();

    if (control == NULL || control->type != CONTROL_WHILE)
    {
        error("REPEAT without WHILE");
        return FALSE;
    }

    branch = compile_branch(OP_BRANCH);
    if (branch == NULL)
    {
        return FALSE;
    }

    branch->arg.branch_target =
        control->target;

    control->branch_instruction->arg.branch_target =
        current_definition->impl.colon.length;

    --csp;

    return TRUE;
}

static int add_builtin(Token name,
                       word_func_t function,
                       word_flags_t flags)
{
    Word* word;

    word = allot_word();
    if (word == NULL)
    {
        error("dictionary full");
        return FALSE;
    }

    word->name = name;
    word->flags = WORD_TYPE_BUILTIN | flags;
    word->impl.builtin = function;

    return TRUE;
}

static int word_to_r(void)
{
    cell_t value;

    REQUIRE_STACK(1);

    if (rsp >= RETURN_STACK_SIZE)
    {
        error("return stack overflow");
        return FALSE;
    }

    POP_UNCHECKED(value);
    RPUSH_UNCHECKED(value);

    return TRUE;
}

static int word_from_r(void)
{
    cell_t value;

    if (rsp == 0)
    {
        error("return stack underflow");
        return FALSE;
    }

    REQUIRE_SPACE(1);

    RPOP_UNCHECKED(value);
    PUSH_UNCHECKED(value);

    return TRUE;
}

static int word_r_fetch(void)
{
    if (rsp == 0)
    {
        error("return stack underflow");
        return FALSE;
    }

    REQUIRE_SPACE(1);

    PUSH_UNCHECKED(return_stack[rsp - 1]);

    return TRUE;
}

static int word_dot_rs(void)
{
    idx_t i;

    printf("<R:%u> ", (unsigned)rsp);

    for (i = 0; i < rsp; ++i)
    {
        printf("%d ", return_stack[i]);
    }

    putchar('\n');

    return TRUE;
}

static int word_do(void)
{
    Instruction* instruction;

    if (state != STATE_COMPILE)
    {
        error("DO is compile-only");
        return FALSE;
    }

    instruction = compile_instruction(OP_DO);
    if (instruction == NULL)
    {
        return FALSE;
    }

    instruction->arg.branch_target = 0; /* patched by loop */

    return push_control(CONTROL_DO,
                        instruction,
                        current_definition->impl.colon.length);
}

static int word_loop(void)
{
    ControlEntry* control;
    Instruction* instruction;

    if (state != STATE_COMPILE)
    {
        error("LOOP is compile-only");
        return FALSE;
    }

    control = top_control();

    if (control == NULL || control->type != CONTROL_DO)
    {
        error("LOOP without DO");
        return FALSE;
    }

    instruction = compile_instruction(OP_LOOP);
    if (instruction == NULL)
    {
        return FALSE;
    }

    instruction->arg.branch_target = control->target;

    /*
     * Patch OP_DO to jump to the instruction after OP_LOOP
     * when start == limit.
     */
    control->branch_instruction->arg.branch_target =
        current_definition->impl.colon.length;

    --csp;

    return TRUE;
}

static int word_i(void)
{
    Instruction* instruction;

    if (state != STATE_COMPILE)
    {
        error("I is compile-only");
        return FALSE;
    }

    instruction = compile_instruction(OP_I);
    return instruction != NULL;
}

static int word_j(void)
{
    Instruction* instruction;

    if (state != STATE_COMPILE)
    {
        error("J is compile-only");
        return FALSE;
    }

    instruction = compile_instruction(OP_J);
    return instruction != NULL;
}

static int word_plus_loop(void)
{
    ControlEntry* control;
    Instruction* instruction;

    if (state != STATE_COMPILE)
    {
        error("+LOOP is compile-only");
        return FALSE;
    }

    control = top_control();

    if (control == NULL || control->type != CONTROL_DO)
    {
        error("+LOOP without DO");
        return FALSE;
    }

    instruction = compile_instruction(OP_PLUS_LOOP);
    if (instruction == NULL)
    {
        return FALSE;
    }

    instruction->arg.branch_target = control->target;

    control->branch_instruction->arg.branch_target =
        current_definition->impl.colon.length;

    --csp;

    return TRUE;
}

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
    add_builtin(TEXT_LITERAL(";"), word_semicolon, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL("words"), word_words, 0);
    add_builtin(TEXT_LITERAL("see"), word_see, 0);
    add_builtin(TEXT_LITERAL("if"), word_if, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL("else"), word_else, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL("then"), word_then, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL("begin"), word_begin, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL("until"), word_until, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL("while"), word_while, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL("repeat"), word_repeat, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL(">r"), word_to_r, 0);
    add_builtin(TEXT_LITERAL("r>"), word_from_r, 0);
    add_builtin(TEXT_LITERAL("r@"), word_r_fetch, 0);
    add_builtin(TEXT_LITERAL(".rs"), word_dot_rs, 0);
    add_builtin(TEXT_LITERAL("do"), word_do, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL("loop"), word_loop, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL("i"), word_i, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL("j"), word_j, WORD_FLAG_IMMEDIATE);
    add_builtin(TEXT_LITERAL("+loop"), word_plus_loop, WORD_FLAG_IMMEDIATE);
}

static int process_input_buffer(void)
{
    Token token;

    tokeniser_pos = 0;

    while (next_token(&token))
    {
        if (!process_token(&token))
        {
            if (state == STATE_COMPILE)
            {
                abort_definition();
            }

            return FALSE;
        }
    }

    return TRUE;
}

int main(void)
{
    int interactive;

    interactive = STDIN_IS_INTERACTIVE();

    if (interactive)
    {
        printf("ltforth %s\n", VERSION);
    }

    init_dictionary();

    for (;;)
    {
        if (interactive)
        {
            printf(state == STATE_COMPILE ? "... " : "> ");
            fflush(stdout);
        }

        if (fgets(input_buffer, LINE_SIZE, stdin) == NULL)
        {
            if (state == STATE_COMPILE)
            {
                error("unfinished definition");
                abort_definition();
            }

            break;
        }

        if (process_input_buffer() && interactive)
        {
            printf("OK\n");
        }
    }

    return 0;
}
