{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Checking this module checks the whole development.
-- Ledger E-4.
module Choreographic.All where

import Choreographic.Party
import Choreographic.Instances          -- instantiates Global/Local/Projection/KCut/Kripke/Bound/Transport
import Choreographic.Swap               -- (parametric; instantiated in Instances.Diamond)
import Choreographic.Operational        -- (parametric; instantiated in Instances.GradeNotStateInvariant)
import Choreographic.Async              -- (parametric; instantiated in Instances, with AsyncKnowledge
import Choreographic.AsyncKnowledge     --  and AsyncBound)
import Choreographic.AsyncBound
import Choreographic.Base.RoleGraded
