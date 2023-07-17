{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    pre-commit-hooks = {
      url = "github:cachix/pre-commit-hooks.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    pre-commit-hooks,
  }:
    with flake-utils.lib;
      eachDefaultSystem (system: let
        pkgs = nixpkgs.legacyPackages.${system};
        hpkgs = pkgs.haskell.packages.ghc94;
        pre-commit = pre-commit-hooks.lib.${system}.run {
          src = ./.;
          hooks = {
            alejandra.enable = true;
            ormolu.enable = true;
            hpack.enable = true;
          };
          tools = {
            ## NOTE: We want Ormolu to be exactly the one provided by HLS, but
            ## this Ormolu is actually a dependency of `hls-ormolu-plugin`,
            ## itself a dependency of HLS. We therefore define a function
            ## `getDeps` that gathers direct Haskell build dependencies and we
            ## use it to go get our Ormolu.
            ormolu = let
              getDeps = p:
                builtins.listToAttrs (map (dependency:
                  pkgs.lib.nameValuePair dependency.pname dependency)
                p.passthru.getBuildInputs.haskellBuildInputs);
            in
              (getDeps
                (getDeps
                  hpkgs.haskell-language-server)
                .hls-ormolu-plugin)
              .ormolu;
          };
        };
      in {
        formatter = pkgs.alejandra;
        devShells = {
          default = pkgs.mkShell {
            ## NOTE: `haskell-language-server` provides Ormolu, so there is no
            ## need to add it here. If it did not, we would have to resort to a
            ## trick such as the one used in `pre-commit-hooks`'s configuration
            ## above.
            buildInputs = with hpkgs; [ghc hpack cabal-install haskell-language-server];
            inherit (pre-commit) shellHook;
          };
        };
      });
}
