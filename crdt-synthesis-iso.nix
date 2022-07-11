{ config, options, lib, pkgs, ...}:

let
  poetry2nixLatest = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/2a2193eb0677a8801c3b414f67bacf499bd0b6fc.tar.gz) {
    system = pkgs.system;
    config = pkgs.config;
  };
in lib.mkMerge [{
  environment.systemPackages = with pkgs; [
    (poetry2nixLatest.poetry2nix.mkPoetryEnv {
      python = python38;
      projectDir = ./.;
      preferWheels = true;
    })

    cvc5
    gnumake
    cmake
    llvm_11
    llvm_11.dev
    clang_11

    racket
  ];

  users = {
    mutableUsers = false;
    allowNoPasswordLogin = true;

    users = {
      demo = {
        home = "/home/demo";
        password = "demo";
        extraGroups = [ "wheel" ];
        isNormalUser = true;
      };
    };
  };

  security.sudo.wheelNeedsPassword = false;

  boot.postBootCommands = let source =
    let
      gitignoreSrc = pkgs.fetchFromGitHub { 
        owner = "hercules-ci";
        repo = "gitignore.nix";
        # put the latest commit sha of gitignore Nix library here:
        rev = "bff2832ec341cf30acb3a4d3e2e7f1f7b590116a";
        # use what nix suggests in the mismatch message here:
        hash = "sha256-kekOlTlu45vuK2L9nq8iVN17V3sB0WWPqTTW3a2SQG0=";
      };
      inherit (import gitignoreSrc { inherit (pkgs) lib; }) gitignoreSource;
    in pkgs.lib.cleanSourceWith
      { filter = (path: type:
          ! (builtins.any
            (r: (builtins.match r (builtins.baseNameOf path)) != null)
            [
              "tests"
              "website"
            ])
        );
        src = gitignoreSource ./.;
      } ;
  in ''
    echo "Loading source code for the artifact"

    ${pkgs.rsync}/bin/rsync -r --owner --group --chown=demo:users --perms --chmod=u+rw ${source}/ /home/demo

    mkdir -p /home/demo/.racket/8.5/pkgs
    ln -s ${./iso-racket-links.rktd} /home/demo/.racket/8.5/links.rktd
    ln -s ${./rosette-packages}/* /home/demo/.racket/8.5/pkgs/

    rm /home/demo/.racket/8.5/pkgs/rosette
    ${pkgs.rsync}/bin/rsync -r --owner --group --chown=demo:users --perms --chmod=u+rw ${./rosette-packages}/rosette/ /home/demo/.racket/8.5/pkgs/rosette
    mkdir /home/demo/.racket/8.5/pkgs/rosette/bin
    ln -s ${(pkgs.z3.overrideAttrs(self: {
      version = "4.8.8";

      src = pkgs.fetchFromGitHub {
        owner = "Z3Prover";
        repo = "z3";
        rev = "z3-4.8.8";
        hash = "sha256-qpmi75I27m89dhKSy8D2zkzqKpLoFBPRBrhzDB8axeY=";
      };
    }))}/bin/z3 /home/demo/.racket/8.5/pkgs/rosette/bin/z3
  '';

  services.getty.autologinUser = "demo";

  services.xserver.enable = true;
  services.xserver.displayManager.startx.enable = true;
} (lib.optionalAttrs (builtins.hasAttr "virtualbox" options) {
  nixpkgs.config = {
    allowUnfree = true;
  };

  virtualbox.vmName = "OOPSLA CRDT Synthesis Artifact";
  virtualbox.memorySize = 1024 * 4;
  virtualbox.params.cpus = 8;

  services.xserver.displayManager.startx.enable = pkgs.lib.mkForce false;
  services.xserver.desktopManager.gnome.enable = true;
  services.xserver.displayManager.gdm.enable = true;

  environment.systemPackages = with pkgs; [
    vscode
    htop
    vim
    nano
    sublime
  ];
})]
