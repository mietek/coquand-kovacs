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


-- The syntax of STLC, with simple products.
import STLC1.Syntax

-- An extension of Kovacs 2017.
import STLC1.Kovacs.Embedding
import STLC1.Kovacs.Substitution
import STLC1.Kovacs.NormalForm
import STLC1.Kovacs.Normalisation
import STLC1.Kovacs.Convertibility
import STLC1.Kovacs.Completeness
import STLC1.Kovacs.PresheafRefinement
import STLC1.Kovacs.Soundness


--------------------------------------------------------------------------------


-- The syntax of STLC, with simple products and coproducts.
import STLC2.Syntax

-- An extension of Kovacs 2017.
import STLC2.Kovacs.Embedding
import STLC2.Kovacs.Substitution
import STLC2.Kovacs.NormalForm
import STLC2.Kovacs.Normalisation.SoundNotComplete
import STLC2.Kovacs.Normalisation.Experimental
import STLC2.Kovacs.Normalisation
import STLC2.Kovacs.Convertibility
import STLC2.Kovacs.Completeness           -- TODO: Finish this
-- import STLC2.Kovacs.PresheafRefinement  -- TODO: Start this
-- import STLC2.Kovacs.Soundness           -- TODO: Start this


--------------------------------------------------------------------------------
