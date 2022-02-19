let
  pkgs = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/nixos-21.11.tar.gz) { };
  unstable = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/nixos-unstable.tar.gz) { };
in
with pkgs;

mkShell {
  venvDir = "./.venv";
  buildInputs = [
    (python38.withPackages (p: with p; [
      pyparsing
    ]))

    cmake
    llvm_11
    clang_11
  ];

  hardeningDisable = [ "fortify" ];

  NIX_LD_LIBRARY_PATH = lib.makeLibraryPath [
    stdenv.cc.cc
  ];

  NIX_LD = lib.fileContents "${stdenv.cc}/nix-support/dynamic-linker";

  PYTHONPATH="llvmlite";
}
