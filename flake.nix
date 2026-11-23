{
  description = "verifylab: TLA+ vs Bend";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05"; # the VPS runs 26.05 (Yarara)
    flake-utils.url = "github:numtide/flake-utils";
    bend.url = "github:bendlang/bend";
    bend.inputs.nixpkgs.follows = "nixpkgs";
  };
  outputs = { self, nixpkgs, flake-utils, bend }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        # `bend --verdict` needs Lean exactly 4.34.0; nixpkgs has 4.29.1, so pin the official release by hash.
        # shortcut: only aarch64-darwin is built and tested, the Linux entries are untested; x86_64-darwin has no release asset.
        leanAssets = {
          aarch64-darwin = { asset = "darwin_aarch64"; hash = "sha256-afJj+m4hu8JGa7+xr/zZJHnuJxTIg6B95UjgmaWSKTI="; };
          x86_64-linux = { asset = "linux"; hash = "sha256-yqqYNWCYyF3A/LvSjh7GbznrZVGCmXK3Uv8g4ShrZGs="; };
          aarch64-linux = { asset = "linux_aarch64"; hash = "sha256-QLBP23+4SdPIDhDDu+68e3NUttPwdFC5FowhSbQNKoI="; };
        };
        lean = let a = leanAssets.${system}; in pkgs.stdenv.mkDerivation rec {
          pname = "lean4-bin";
          version = "4.34.0";
          src = pkgs.fetchurl {
            url = "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-${a.asset}.tar.zst";
            hash = a.hash;
          };
          nativeBuildInputs = [ pkgs.zstd ] ++ pkgs.lib.optional pkgs.stdenv.isLinux pkgs.autoPatchelfHook;
          buildInputs = pkgs.lib.optionals pkgs.stdenv.isLinux [ pkgs.stdenv.cc.cc.lib pkgs.zlib ];
          sourceRoot = "lean-${version}-${a.asset}";
          dontConfigure = true;
          dontBuild = true;
          dontFixup = !pkgs.stdenv.isLinux; # leave the signed macOS binaries untouched
          installPhase = "mkdir -p $out && cp -r . $out";
        };
      in {
        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.go pkgs.gopls pkgs.sqlite
            pkgs.tlaplus18 # TLC 1.8.0 on the default JRE; `tlaplus` is 1.7.4 on jre8
            pkgs.just pkgs.hyperfine pkgs.jq
            bend.packages.${system}.default
          ] ++ pkgs.lib.optional (leanAssets ? ${system}) lean;
        };
      });
}
