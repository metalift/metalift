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
    pyparsing
  ]))

  cvc5
  cmake
  llvm_11
  clang_11
]
