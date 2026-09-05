{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module Everything where

import ALMA.Cosmos.ContCategory
import ALMA.Cosmos.ContCategoryLemmas
import ALMA.Cosmos.ContFunctor
import ALMA.Cosmos.ContCatEquiv
import ALMA.Cosmos.ContCatEquivFunctor
import ALMA.Cosmos.Unfolding
import ALMA.Cosmos.MorphismObject
import ALMA.Cosmos.ContCatEquivLemmas
import ALMA.Cosmos.MorphismMorphism
import ALMA.Cosmos
import ALMA.Cosmos.Terminal
import ALMA.Cosmos.CoalgCat
import ALMA.Cosmos.Lambek
import ALMA.Cosmos.MorphismCorrespondence
import ALMA.Cosmos.ListCosmos
import ALMA.Cosmos.CosmosCategory
import ALMA.Cosmos.Closure

import ALMA.InitialPass.ObjEquivCat
import ALMA.InitialPass.ObjEquivFunctor
import ALMA.InitialPass.ContCategory
import ALMA.InitialPass.ContCategoryLemmas
import ALMA.InitialPass.ContCatEquiv
import ALMA.InitialPass.ContCatEquivFunctor
import ALMA.InitialPass.Unfolding
import ALMA.InitialPass.MorphismObject
import ALMA.InitialPass.ContCatEquivLemmas
import ALMA.InitialPass.MorphismMorphism
import ALMA.InitialPass.Cosmos

import ALMA.Prototype.Prelude
import ALMA.Prototype.Cosmos
import ALMA.Prototype.Indestructibility
import ALMA.Prototype.Beings
import ALMA.Prototype.Universe
import ALMA.Prototype.StandardModel
-- A subst-related complexity issue was encountered in the proof of comp-cong-≃⇒ℱ, which left a hole in the development
-- 遭遇comp-cong-≃⇒ℱ 证明中的 subst 复杂性问题，留下了一个洞
-- import ALMA.Prototype.Properties
