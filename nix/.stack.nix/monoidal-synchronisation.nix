{ system
  , compiler
  , flags
  , pkgs
  , hsPkgs
  , pkgconfPkgs
  , errorHandler
  , config
  , ... }:
  {
    flags = {};
    package = {
      specVersion = "2.4";
      identifier = { name = "monoidal-synchronisation"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "2021 Input Output (Hong Kong) Ltd.";
      maintainer = "coot@coot.me";
      author = "Marcin Szamotulski";
      homepage = "";
      url = "";
      synopsis = "";
      description = "";
      buildType = "Simple";
      isLocal = true;
      };
    components = {
      "library" = {
        depends = [ (hsPkgs."base" or (errorHandler.buildDepError "base")) ];
        buildable = true;
        };
      tests = {
        "test" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            (hsPkgs."io-classes" or (errorHandler.buildDepError "io-classes"))
            (hsPkgs."io-sim" or (errorHandler.buildDepError "io-sim"))
            (hsPkgs."monoidal-synchronisation" or (errorHandler.buildDepError "monoidal-synchronisation"))
            ];
          buildable = true;
          };
        };
      };
    } // {
    src = (pkgs.lib).mkDefault (pkgs.fetchgit {
      url = "https://github.com/input-output-hk/ouroboros-network";
      rev = "e9cda57df7ea6969edbc3bfc4e117668277d09c8";
      sha256 = "1a91z6yvlhzlqrf7fy51fmmpm3ssk684h6pjgg022cdlsq56yif2";
      }) // {
      url = "https://github.com/input-output-hk/ouroboros-network";
      rev = "e9cda57df7ea6969edbc3bfc4e117668277d09c8";
      sha256 = "1a91z6yvlhzlqrf7fy51fmmpm3ssk684h6pjgg022cdlsq56yif2";
      };
    postUnpack = "sourceRoot+=/monoidal-synchronisation; echo source root reset to \$sourceRoot";
    }