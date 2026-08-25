{
  description = "A standard library for use with the Agda compiler";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs?ref=nixos-26.05";
  };

  outputs = inputs: {
    packages = builtins.mapAttrs (_: pkgs: {
      default = pkgs.agdaPackages.mkDerivation {
        pname = "standard-library";
        version = "2.4.0";
        src = ./.;

        meta = with pkgs.lib; {
          homepage = "https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary";
          description = "A standard library for use with the Agda compiler";
          license = licenses.mit;
          platforms = platforms.unix;
          # Maintainers for the upstream nixpkgs package, which code I just copied
          maintainers = with maintainers; [ jwiegley mudri alexarice turion ];
        };
      };
    }) inputs.nixpkgs.legacyPackages;
    
    devShells = builtins.mapAttrs (_: pkgs: {
      default = pkgs.mkShell { buildInputs = [ pkgs.agda ]; };
    }) inputs.nixpkgs.legacyPackages;
  };
}
