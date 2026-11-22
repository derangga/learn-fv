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
      let pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.go pkgs.gopls pkgs.sqlite
            pkgs.tlaplus18 # TLC 1.8.0 on the default JRE; `tlaplus` is 1.7.4 on jre8
            pkgs.just pkgs.hyperfine pkgs.jq
            bend.packages.${system}.default
          ];
        };
      });
}
