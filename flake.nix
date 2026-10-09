{
  description = "SMT-Rex, an SMT solver";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
      cli = builtins.fromTOML (builtins.readFile ./cli/Cargo.toml);
    in
    {
      packages = forAll (pkgs: rec {
        smt-rex = pkgs.rustPlatform.buildRustPackage {
          pname = "smt-rex";
          version = cli.package.version;
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          cargoBuildFlags = [ "-p" "smtrex-cli" ];
          cargoTestFlags = [ "--workspace" ];
          meta = {
            description = "SMT solver for QF_UF, QF_LRA, QF_LIA, QF_NRA and QF_BV";
            mainProgram = "smt-rex";
            license = with pkgs.lib.licenses; [ mit asl20 ];
          };
        };
        default = smt-rex;
      });

      devShells = forAll (pkgs: {
        default = pkgs.mkShell {
          packages = with pkgs; [ cargo rustc clippy rustfmt rust-analyzer z3 cvc5 python3 zstd ];
        };
      });

      checks = forAll (pkgs: {
        smt-rex = self.packages.${pkgs.stdenv.hostPlatform.system}.smt-rex;
      });
    };
}
