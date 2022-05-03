let
  pkgs = import <nixpkgs> {};
  unstable = import <nixos-unstable> {};
in
with pkgs;

mkShell {
  buildInputs = [
    (python38.withPackages (p: with p; [
      poetry
    ]))

    unstable.cvc5
    llvm_11
    clang_11
  ];

  shellHook = ''
    poetry install
    source .venv/bin/activate
  '';

  hardeningDisable = [ "fortify" ];

  NIX_LD_LIBRARY_PATH = lib.makeLibraryPath [
    stdenv.cc.cc
  ];

  NIX_LD = lib.fileContents "${stdenv.cc}/nix-support/dynamic-linker";
}
