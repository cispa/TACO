# Setup and Installation

## Prerequisites

### Supported SMT Solvers

TACO internally uses SMT solvers for the model checking. However, it does not
ship with any solvers by default.
Currently, TACO will check whether Z3 or CVC5 is installed on your system. If
you do not have a favorite SMT solver we recommend you install
[CVC5](https://github.com/cvc5/cvc5) and/or [Z3](https://github.com/Z3Prover/z3).

You can also use a custom SMT solver when verifying systems with TACO. You can
find more details on how to configure a custom solver in section
[Using a custom SMT solver](./advanced-configuration.md#using-a-custom-smt-solver).

<details> <summary><b>Z3 Installation Instructions</b></summary>

Many package managers have a package for Z3, for example, you can install
Z3 on Debian-based Linux distributions (like Ubuntu) using:

```bash
sudo apt-get install z3
```

or under MacOS using [homebrew](https://brew.sh/) with:

```bash
brew install z3
```

For other operating systems consult your package manager or check the [Z3
documentation](https://microsoft.github.io/z3guide/).

</details>

<details> <summary><b>CVC5 Installation Instructions</b></summary>

Many package managers have a package for CVC5, for example, you can install
CVC5 on Debian-based Linux distributions (like Ubuntu) using:

```bash
sudo apt-get install cvc5
```

Under MacOS there exists a cask in the cvc5 GitHub organization
([see](https://github.com/cvc5/homebrew-cvc5)) which you can use with
[homebrew](https://brew.sh/) with:

```bash
brew install --cask cvc5/cvc5/cvc5
```

For other operating systems consult your package manager or check the [CVC5
download page](https://cvc5.github.io/downloads.html).

</details>

(visualization-installing-graphviz)=

### Visualization: Installing Graphviz

Currently, the tool only supports a simple visualization of threshold automata
by encoding the threshold automata into graphs encoded in the
[`DOT` Language](https://graphviz.org/doc/info/lang.html).

This format can be converted into an image using the
[`graphviz` library](https://graphviz.org/).

The tool provides a convenient CLI command `visualize`. However, to output `svg`
or `png` the [`graphviz` library](https://graphviz.org/) must already be
installed on your system. Otherwise, you can always export an automaton into
the `dot` format and use a compatible visualization tool.

<details> <summary><b>Graphviz Library Installation</b></summary>

On Debian / Ubuntu you can use

```bash
sudo apt-get install graphviz
```

to install `graphviz` or under MacOS use [homebrew](https://brew.sh/) with:

```bash
brew install graphviz
```

For other operating systems please consult the
[official graphviz download page](https://graphviz.org/download/).

</details>

## Installation

TACO can be installed using [`cargo`](https://doc.rust-lang.org/cargo/), the
Rust package manager (and a working Rust installation).
If cargo (and Rust) is not yet installed on your system, you can follow the
instructions of the official
[Rust installation](https://rust-lang.org/tools/install/) guide.

Once cargo is installed, you can install TACO by running

```bash
cargo install taco-cli --locked
```

Now the `taco-cli` command should be available on your system. You can test the
installation by running

```bash
taco-cli --version
```
