let
  pkgs = import <nixpkgs> {};
  unstable = import <nixos-unstable> {};
in
with pkgs;

let
  cvc5 = callPackage ./cvc5.nix { unstable = unstable; };
in
mkShell {
  venvDir = "./.venv";
  buildInputs = [
    python38Packages.venvShellHook
    python38Packages.llvmlite
    python38Packages.pyparsing
    python38Packages.black
    python38Packages.mypy

    cvc5
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
