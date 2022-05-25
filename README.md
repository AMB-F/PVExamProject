# Exam submission for the Ghost Variables 

This repository contains the exam submission in the Program Verification course held at ITU in the spring of 2022.

# Installation

In order to run this project, you need to have the *infotheo* and *math-comp* Coq libraries installed and accessible from your Coq installation.

You can read on how to install these libraries here:

- [infotheo](https://github.com/affeldt-aist/infotheo#building-and-installation-instructions)
- [math-comp](https://math-comp.github.io/installation.html)

Additionally, you need to have `make` installed.

## Cleaning

Should you want to clean all of the compiled files in the `PV` directory, you can run the following command:

```bash
make clean
```

# Running

The main part of this project is located in the `PV/Approach1.v` and `PV/Approach2.v` files. You're recommended to run the following commands in your terminal to compile the necessary files:

```
coq_makefile -f _CoqProject -o Makefile
make
```

# References:
The code contained in `PV/Approach1.v` and `PV/Approach2.v` is heavily based on the code from

- [Software Foundations 1: Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/toc.html), Imp.v. Maps.v
- [Software Foundations 2: Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/toc.html), Hoare.v

Both by Benjamin C. Pierce, et al. 2021.


The base of this code has been taken directly from these files, and some code has been taken and edited to fit our project.

All additions and edits to the code has been by, or in coorporation with, ITU associate professor Alessandro Bruni.
The project has been supervised by course teacher Jesper Bengtson.

Code comments are provided to indicate authorship of the code. 'Edited' mean code taken and edited from the books, no comment means code taken directly from the book.
