{
  description = "katara";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.05";
  inputs.poetry2nix-flake = {
    url = "github:nix-community/poetry2nix";
    inputs.nixpkgs.follows = "nixpkgs";
  };

  inputs.llvmlite-patched = {
    flake = false;
    url = "https://github.com/metalift/llvmlite.git";
    type = "git";
    ref = "patched-metalift";
  };

  outputs = { self, nixpkgs, flake-utils, poetry2nix-flake, llvmlite-patched }: (flake-utils.lib.eachDefaultSystem (system:
    with import nixpkgs {
      inherit system;
      overlays = [ poetry2nix-flake.overlay ];
    };

    {
      devShell = mkShell {
        buildInputs = [
          (poetry2nix.mkPoetryEnv {
            python = python38;
            projectDir = ./.;

            overrides = poetry2nix.overrides.withDefaults (_: poetrySuper: {
              autoflake = poetrySuper.autoflake.overrideAttrs(_: super: {
                nativeBuildInputs = super.nativeBuildInputs ++ [ poetrySuper.hatchling ];
              });
            });
          })

          cvc5
          cmake
          llvm_11
          clang_11
        ];
      };
    }
  ));
}
