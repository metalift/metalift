let
  pkgs = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/nixos-21.11.tar.gz) { };
  unstable = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/nixos-unstable.tar.gz) { };
in
with pkgs;

let
  cvc5 = callPackage ./cvc5.nix { unstable = unstable; };
in
mkShell {
  venvDir = "./.venv";
  buildInputs = [
    (python38.withPackages (p: with p; [
      pyparsing
    ]))

    cvc5
    cmake
    llvm_11
    clang_11
  ];

  hardeningDisable = [ "fortify" ];

  PYTHONPATH="llvmlite";
}
