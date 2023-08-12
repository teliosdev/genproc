# PreProc

**PreProc** is a command line tool to run preprocessor directives in a file.
It's pretty simple, and is meant to be an analogue to the C preprocessor; but
less fixated on C.

## Usage

```
preproc [options] <input file> -o <output file>
```

The `<input file>` is the file to run the preprocessor on. The `-o` option
specifies the output file. If the output file is not specified, the output will
be written to stdout.

The input file should be a UTF-8 text file.  Each line is processed separately;
if the line starts with a preprocessor directive prefix, the line is parsed
as a preprocessor directive.  Otherwise, the line is written to the output
file.  The preprocessor directive prefix is `#` by default, though is
determined by the file extension, but can be changed with the `-c`/`--comment`
option.

There are two main tables of values: the definition table, and the replacement
table.  The definition table is a table of variables and their values, when
used in expressions.  The replacement table is a table of variables and their
values, and the corresponding patterns in the non-directive text are replaced
with the value of the variable.  By default, definitions are not replacements;
however, you can declare a replacement with `#replace`.

The current available preprocessor directives are:

- `#if <expr>`: If the expression evaluates to true, the following lines
  are passed through.  Otherwise, they are ignored.
- `#elsif <expr>`: If all of the previous `#if` or `#elsif` evaluated to
  false, and this expression evaluates to true, the following lines are
  passed through.  Otherwise, they are ignored.
- `#else`: If all of the previous `#if` or `#elsif` evaluated to false,
  the following lines are passed through.  Otherwise, they are ignored.
- `#endif`: Ends the previous `#if`, `#elsif`, or `#else` block.
- `#replace <name>`: Replaces all instances of `name` with the value of
  the variable `name`.  If the variable is not defined, it is replaced
  with the empty string.
- `#replace <name> <expr>`: Replaces all instances of `name` in the text
  with the value of the expression `expr`.  If the expression cannot be
  evaluated, it is replaced with the empty string.
- `#unrep <name>`: Stops substitution of `name` in the current scope.
- `#define <name> <expr>`: Defines the variable `name` to be the value
  of the expression `expr`.  If the expression cannot be evaluated, the
  variable is set to null.
- `#error <expr>`: Marks the current line as an error.  If the expression
  cannot be evaluated, the error is marked as `null`.  This will cause
  the preprocessor to exit with an error code, after processing the whole
  file.

## Examples

To demonstrate the definitions and replacements as expressed above, an example
input file is:

```
#define WORLD "world"
hello, WORLD!
#replace WORLD
hello, WORLD!
#replace WORLD null
hello, WORLD!
```

The output of processing this file is:

```
hello, WORLD!
hello, world!
hello, !
```

# Why?

Because.

I wanted to write it.

# Is it any good?

Yes.
