// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.gobra.ast.internal

import viper.gobra.ast.internal.utility.Nodes
import viper.gobra.reporting.Source
import viper.silver.ast.utility.Visitor
import viper.silver.ast.utility.rewriter.Traverse.Traverse
import viper.silver.ast.utility.rewriter.{StrategyBuilder, Traverse}
import viper.silver.{ast => vpr}

import scala.collection.mutable
import scala.reflect.ClassTag

class EncodingConfig (val slices:Integer= 0) {
def config (): String = {
    ("$"+slices )
}}

