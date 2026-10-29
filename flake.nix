{
  description = "eval";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs =
    { self, nixpkgs, ... }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-darwin" ];
      forallSystems =
        f:
        nixpkgs.lib.genAttrs supportedSystems (
          system:
          f (rec {
            inherit system;
            pkgs = nixpkgsFor system;
            haskellPackages = hpkgsFor system pkgs;
          })
        );
      nixpkgsFor = system: import nixpkgs { inherit system; };
      hpkgsFor =
        system: pkgs:
        with pkgs.haskell.lib;
        pkgs.haskell.packages.ghc912.override {
          overrides = self: super: {
            # unicode-data's test suite expects Unicode 15.1 tables; GHC 9.12's
            # base ships Unicode 16, so the tests fail although the library is fine.
            unicode-data = dontCheck super.unicode-data;
        }; };
    in
    {
      packages = forallSystems (
        {
          system,
          pkgs,
          haskellPackages,
        }:
        {
          eval = haskellPackages.callCabal2nix "eval" ./. { };
          default = self.packages.${system}.eval;
        }
      );
      devShells = forallSystems (
        {
          system,
          pkgs,
          haskellPackages,
        }:
        {
          eval = haskellPackages.shellFor {
            packages = p: [ self.packages.${system}.eval ];
            buildInputs = with haskellPackages; [
              cabal-install
              haskell-language-server
            ];
            withHoogle = true;
          };
          default = self.devShells.${system}.eval;
        }
      );
    };
}
