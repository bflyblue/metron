{- | Unicode entry by name, Julia-style (design §2.8, §7.3): in the REPL,
@\\mu@ followed by TAB becomes @μ@. Every result here is either a spelling
the lexer maps to the same tokens as an ASCII form in the §2.8 table, or a
letter that is a valid identifier character; the test suite checks that
against "Metron.Lexer". The lexer's own table stays the authority.
-}
module Metron.Unicode (
  completions,
  lookupName,
  matching,
) where

import Data.Text (Text)
import Data.Text qualified as T

{- | Name (without the backslash) to the text it stands for, in the order
the REPL lists them.
-}
completions :: [(Text, Text)]
completions =
  operators
    ++ marks
    ++ greek
    ++ [ ("^" <> T.singleton d, T.singleton s) | (d, s) <- zip ['0' .. '9'] "⁰¹²³⁴⁵⁶⁷⁸⁹"
       ]
    ++ [("^-", "⁻")]
    ++ [ ("_" <> T.singleton d, T.singleton s) | (d, s) <- zip ['0' .. '9'] "₀₁₂₃₄₅₆₇₈₉"
       ]
 where
  operators =
    [ ("to", "→")
    , ("rightarrow", "→")
    , ("otimes", "⊗")
    , ("cdot", "·")
    , ("times", "×")
    , ("odot", "⊙")
    , ("oslash", "⊘")
    , ("div", "÷")
    , ("le", "≤")
    , ("leq", "≤")
    , ("ge", "≥")
    , ("geq", "≥")
    , ("ne", "≠")
    , ("neq", "≠")
    , ("or", "∨")
    , ("vee", "∨")
    , ("neg", "¬")
    , ("lnot", "¬")
    , ("wedge", "∧")
    , ("star", "⋆")
    , ("pm", "±")
    , ("pms", "±σ")
    , ("sqrt", "√")
    , ("circ", "∘")
    ]
  marks =
    [ ("deg", "°")
    , ("degC", "°C")
    , ("degF", "°F")
    , ("prime", "′")
    , ("dprime", "″")
    , ("pprime", "″")
    , -- The forms the lexer folds the micro and ohm signs to (design §2.1).
      ("micro", "\x03BC")
    , ("ohm", "\x03A9")
    ]
  -- Capitals that look like Latin letters are left out: they would be
  -- identifiers distinct from the Latin ones.
  greek =
    [ ("alpha", "α")
    , ("beta", "β")
    , ("gamma", "γ")
    , ("delta", "δ")
    , ("epsilon", "ε")
    , ("zeta", "ζ")
    , ("eta", "η")
    , ("theta", "θ")
    , ("iota", "ι")
    , ("kappa", "κ")
    , ("lambda", "λ")
    , ("mu", "\x03BC")
    , ("nu", "ν")
    , ("xi", "ξ")
    , ("pi", "π")
    , ("rho", "ρ")
    , ("sigma", "σ")
    , ("tau", "τ")
    , ("upsilon", "υ")
    , ("phi", "φ")
    , ("chi", "χ")
    , ("psi", "ψ")
    , ("omega", "ω")
    , ("Gamma", "Γ")
    , ("Delta", "Δ")
    , ("Theta", "Θ")
    , ("Lambda", "Λ")
    , ("Xi", "Ξ")
    , ("Pi", "Π")
    , ("Sigma", "Σ")
    , ("Upsilon", "Υ")
    , ("Phi", "Φ")
    , ("Psi", "Ψ")
    , ("Omega", "\x03A9")
    ]

-- | The text a name stands for.
lookupName :: Text -> Maybe Text
lookupName n = lookup n completions

{- | The entries a typed name selects, as Julia does: an exact name alone
(so @pm@ is @±@ although @pms@ exists), otherwise every name it starts.
-}
matching :: Text -> [(Text, Text)]
matching n = case lookupName n of
  Just t -> [(n, t)]
  Nothing -> [e | e@(k, _) <- completions, n `T.isPrefixOf` k]
