#!/usr/bin/env bash
store_path=$1
echo $store_path

store_name=${store_path:11}

nix-store --export $store_path > $store_name.nar
