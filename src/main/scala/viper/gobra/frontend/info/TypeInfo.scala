package viper.gobra.frontend.info

import org.bitbucket.inkytonik.kiama.relation.Tree
import viper.gobra.ast.frontend._
import viper.gobra.frontend.info.base.SymbolTable.Regular
import viper.gobra.frontend.info.base.Type.Type
import viper.gobra.theory.Addressability

trait TypeInfo extends ExternalTypeInfo {

  def context: Info.Context

  def typ(expr: PExpression): Type
  def addressability(expr: PExpression): Addressability
  def addressableVar(id: PIdnNode): Addressability

  def codeRoot(n: PNode): PScope

  def tree: Tree[PNode, PPackage]

  def regular(n: PIdnNode): Regular

  def variables(s: PScope): Vector[PIdnNode]

  def resolve(n: PExpressionOrType): Option[AstPattern.Pattern]
  def exprOrType(n: PExpressionOrType): Either[PExpression, PType]

}
