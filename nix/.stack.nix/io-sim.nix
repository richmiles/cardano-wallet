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
    flags = { asserts = false; };
    package = {
      specVersion = "1.10";
      identifier = { name = "io-sim"; version = "0.2.0.0"; };
      license = "Apache-2.0";
      copyright = "2019-2020 Input Output (Hong Kong) Ltd.";
      maintainer = "";
      author = "Duncan Coutts, Marcin Szamotulski, Alexander Vieth";
      homepage = "";
      url = "";
      synopsis = "A pure simlator for monadic concurrency with STM";
      description = "";
      buildType = "Simple";
      isLocal = true;
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."io-classes" or (errorHandler.buildDepError "io-classes"))
          (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."psqueues" or (errorHandler.buildDepError "psqueues"))
          (hsPkgs."time" or (errorHandler.buildDepError "time"))
          (hsPkgs."quiet" or (errorHandler.buildDepError "quiet"))
          ];
        buildable = true;
        };
      tests = {
        "test" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."array" or (errorHandler.buildDepError "array"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."io-classes" or (errorHandler.buildDepError "io-classes"))
            (hsPkgs."io-sim" or (errorHandler.buildDepError "io-sim"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
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
    postUnpack = "sourceRoot+=/io-sim; echo source root reset to \$sourceRoot";
    }