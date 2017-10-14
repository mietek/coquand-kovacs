module Everything where

import Prelude
import Category


--------------------------------------------------------------------------------


-- The syntax of STLC.
import STLC.Syntax

-- A simplification of Coquand 2002,
-- with de Bruijn indices and implicit substitutions.
import STLC.Coquand.Renaming
import STLC.Coquand.Substitution
import STLC.Coquand.Normalisation   -- TODO: Fill postulates
import STLC.Coquand.Convertibility  -- TODO: Simplify β-reduction rule
import STLC.Coquand.Completeness    -- TODO: Fill postulates
import STLC.Coquand.Soundness       -- TODO: Fill postulates

-- A restyling of Kovacs 2017.
import STLC.Kovacs.Embedding
import STLC.Kovacs.Substitution
import STLC.Kovacs.NormalForm
import STLC.Kovacs.Normalisation
import STLC.Kovacs.Convertibility
import STLC.Kovacs.Completeness
import STLC.Kovacs.PresheafRefinement
import STLC.Kovacs.Soundness


--------------------------------------------------------------------------------


-- The syntax of STLC, extended with products and coproducts.
import STLCE.Syntax

-- An extension of Kovacs 2017.
import STLCE.Kovacs.Embedding
import STLCE.Kovacs.Substitution
import STLCE.Kovacs.NormalForm
import STLCE.Kovacs.Normalisation.SoundNotComplete
import STLCE.Kovacs.Normalisation.Experimental
import STLCE.Kovacs.Normalisation
import STLCE.Kovacs.Convertibility
import STLCE.Kovacs.Completeness           -- TODO: Finish this
-- import STLCE.Kovacs.PresheafRefinement  -- TODO: Start this
-- import STLCE.Kovacs.Soundness           -- TODO: Start this


--------------------------------------------------------------------------------
