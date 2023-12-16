{ stdenv, nix-gitignore, agda }:
stdenv.mkDerivation {
  name = "lin-env";
  src = nix-gitignore.gitignoreSource [] ./.;
  buildInputs = [ (agda.withPackages (ps: [ ps.standard-library ps.agda-categories ]))
		];
  buildPhase = ''
  '';
  installPhase = "";
}
