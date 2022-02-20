#!/usr/bin/env bash

cur_dir=$(pwd)

mkdir ~/nix-cache

cd ~/nix-cache

nix-store --query --references $(nix-instantiate $cur_dir/ci-shell.nix) | \
  xargs nix-store --realise | \
  xargs nix-store --query --requisites | \
  xargs -n 1 $cur_dir/ci-util/write-cache-nar.sh

cd $cur_dir
