with import (fetchTarball https://github.com/NixOS/nixpkgs/archive/nixos-21.05.tar.gz) { };

let
  cvc5 = import (./cvc5.nix);
in [
  (python38.withPackages (p: with p; [
    llvmlite
    pyparsing
  ]))

  cvc5
  llvm_10
  clang_10
  racket
]
