{
  description = "metron";

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
          metron = haskellPackages.callCabal2nix "metron" ./. { };
          default = self.packages.${system}.metron;
        }
      );
      devShells = forallSystems (
        {
          system,
          pkgs,
          haskellPackages,
        }:
        {
          metron = haskellPackages.shellFor {
            packages = p: [ self.packages.${system}.metron ];
            buildInputs = with haskellPackages; [
              cabal-install
              haskell-language-server
            ];
            withHoogle = true;
          };
          default = self.devShells.${system}.metron;
        }
      );
    };
}
