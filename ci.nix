let pkgs = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/nixos-21.05.tar.gz) { };
in
with pkgs;

let
  unstable = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/nixos-unstable.tar.gz) { };
in
let
  cvc5 = callPackage ./cvc5.nix { unstable = unstable; };
in [
  (python38.withPackages (p: with p; [
    llvmlite
    pyparsing
  ]))

  cvc5
  cmake
  llvm_10
  clang_10
  racket
]
