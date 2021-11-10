with import <nixpkgs> {};

let
  unstable = import <nixos-unstable> {};
  pythonPackages = python38Packages;
  cvc5 = import (./cvc5.nix);
in
mkShell {
  venvDir = "./.venv";
  buildInputs = [
    pythonPackages.python
    pythonPackages.llvmlite
    pythonPackages.pyparsing
    (cvc5)
    llvm_10
    clang_10
    racket
  ];

  hardeningDisable = [ "fortify" ];

  NIX_LD_LIBRARY_PATH = lib.makeLibraryPath [
    stdenv.cc.cc
  ];

  NIX_LD = lib.fileContents "${stdenv.cc}/nix-support/dynamic-linker";
}
