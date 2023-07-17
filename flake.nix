{
 inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
 inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib;
    eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        hpkgs = pkgs.haskell.packages.ghc94;
      in {
        devShells = {
          default = pkgs.mkShell {
            buildInputs = with hpkgs; [ ghc hpack cabal-install haskell-language-server ];
          };
        };
      });
}
