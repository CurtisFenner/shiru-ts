# The Shiru Compiler

**Shiru** is an experimental programming language equipped with an SMT solver to
verify assertions and pre-conditions at compile time.

This repository contains the compiler & interpreter for Shiru, written in
TypeScript.

## Building and Running Tests

Clone the project from GitHub, and enter the directory.

```bash
git clone https://github.com/CurtisFenner/shiru-ts.git
cd shiru-ts
```

If you have `yarn` installed, you can use it to run the scripts in
`package.json`.

```bash
yarn run build # builds the compiler
yarn run test # tests the newly built compiler
```

When developing, you can use `yarn build --watch` to automatically recompile
files as they are modified.

## Contributions

The compiler and language is currently unstable and early in developement. I am
not seeking contributions at this time.
