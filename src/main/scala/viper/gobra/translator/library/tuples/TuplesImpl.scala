// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.
package viper.gobra.translator.library.tuples


import viper.silver.{ast => vpr}



class TuplesImpl extends Tuples {

  /**
    * Finalizes translation. `addMemberFn` is called with any member that is part of the encoding.
    */
  override def finalize(addMemberFn: vpr.Member => Unit): Unit = {
    generatedDomains.take(2) foreach addMemberFn
  }

  val domainType = vpr.DomainType ("Struct", Map.empty)(Seq.empty)
  val domain2 = vpr.Domain(name="Struct", typVars= Nil, functions = Seq(vpr.DomainFunc(s"struct_loc", Seq( vpr.LocalVarDecl("s",domainType)(),vpr.LocalVarDecl("m",vpr.Int)()), vpr.Int)(domainName = "Struct")),
    axioms=Nil)()
   
  

  override def create(args: Vector[vpr.Exp])(pos: vpr.Position, info: vpr.Info, errT: vpr.ErrorTrafo): vpr.DomainFuncApp = {
     if (_generatedDomains.size== 0) {addNTuplesDomain(0);}
    
    
    
    val arity = args.size
    
    
  
    if (arity==0) { vpr.DomainFuncApp(
      funcname = "default_tuple",
      args = Seq(vpr.IntLit(0)()),
      typVarMap = Map(vpr.TypeVar("T")->domainType)
    )(pos,info, domainType, s"StructOps",errT)}


    else helper(args, args.size)(pos,info,errT)
  }
  def helper (args: Vector[vpr.Exp], fields:Int)(pos: vpr.Position, info: vpr.Info, errT: vpr.ErrorTrafo): vpr.DomainFuncApp = {
    
    
    
    val arity = args.size
    val index = arity - 1
    
    val indexik = index 
    
      if (arity==1) { vpr.DomainFuncApp(
      funcname = "struct_settup",
      args = Seq(vpr.DomainFuncApp("default_tuple",Seq(vpr.IntLit(fields)()),Map(vpr.TypeVar("T")->args(index).typ))(vpr.NoPosition,vpr.NoInfo,domainType, s"StructOps",vpr.NoTrafos),vpr.IntLit(indexik)(),args(index)),
      typVarMap = Map(vpr.TypeVar("T")->args(index).typ)
    )(pos,info,domainType, s"StructOps",errT)}
 
    else vpr.DomainFuncApp(
      funcname = "struct_settup",
      args = Seq(helper(args.dropRight(1),fields)(vpr.NoPosition,vpr.NoInfo,vpr.NoTrafos),vpr.IntLit(indexik)(),args(index)),
      typVarMap = Map(vpr.TypeVar("T")->args(index).typ)
    )(pos,info, domainType, s"StructOps",errT)








  }



  override def get(arg: vpr.Exp, index: Int, arity: Int)(pos: vpr.Position, info: vpr.Info, errT: vpr.ErrorTrafo): vpr.DomainFuncApp = {
     if (_generatedDomains.size== 0) {addNTuplesDomain(0);}
     
   
    vpr.DomainFuncApp(func = vpr.DomainFunc(s"struct_gettup", Nil, vpr.TypeVar("T"))(domainName = s"StructOps"), Seq(vpr.DomainFuncApp(s"struct_loc", Seq(arg,vpr.IntLit(index)()), typVarMap = Map.empty)(vpr.NoPosition,vpr.NoInfo, vpr.Int, "Struct",vpr.NoTrafos )), typVarMap = Map(vpr.TypeVar("T")->flag(index)))(pos, info, errT)
  
  }

def generatedDomains: List[vpr.Domain] = _generatedDomains

  private var _generatedDomains: List[vpr.Domain] = List.empty
 
  
  
  

  private def addNTuplesDomain(arity: Int): Unit = {
    val domainName = s"Struct"
   val domainName2: String = s"StructOps"
    
    val struct_get =  vpr.DomainFunc(s"struct_gettup", Seq(vpr.LocalVarDecl("l",vpr.Int)()), vpr.TypeVar(s"T"))(domainName = domainName2)
    val struct_lengthtup =  vpr.DomainFunc(s"struct_lengthtup", Seq(vpr.LocalVarDecl("x",domainType)()), vpr.Int)(domainName = domainName2)
    val default =  vpr.DomainFunc(s"default_tuple", Seq(vpr.LocalVarDecl("l",vpr.Int)()), domainType)(domainName = domainName2)
     val struct_rev =   vpr.DomainFunc(s"struct_settup", Seq(vpr.LocalVarDecl("s",domainType)(),vpr.LocalVarDecl("m",vpr.Int)(),vpr.LocalVarDecl("t",vpr.TypeVar(s"T"))()), domainType)(domainName = domainName2)
   

   
  



    // there are not quantified variables for tuples of 0 arity. Thus, do not generate any axioms in this case:
    
  
    
 
    val typeVarsi = Seq(vpr.TypeVar(s"T"))
    val typeVarMapka = (typeVarsi zip typeVarsi).toMap
    val s=vpr.LocalVarDecl("s", domainType)().localVar
    val t=vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))().localVar
    val m=vpr.LocalVarDecl("m", vpr.Int)().localVar
    val n=vpr.LocalVarDecl("n", vpr.Int)().localVar
    
    
val first = {

vpr.NamedDomainAxiom(
        name = s"get_set_0_ax",
        exp = vpr.Forall(
          Seq(vpr.LocalVarDecl("s", domainType)(),vpr.LocalVarDecl("m", vpr.Int)(), vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))()),
          Seq(vpr.Trigger(Seq(vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,m,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo,domainType, domainName2,vpr.NoTrafos ),m), Map.empty)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos )))()),
         vpr.EqCmp(
               vpr.DomainFuncApp(s"struct_gettup", Seq(vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,m,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, domainType, domainName2,vpr.NoTrafos ),m), Map.empty)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos )),typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"T"), domainName2,vpr.NoTrafos ),
                vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))().localVar)()
        )()
      )(domainName = domainName)
}
val second = {
vpr.NamedDomainAxiom(
        name = s"get_set_1_ax",
        exp = vpr.Forall(
          Seq(vpr.LocalVarDecl("s", domainType)(),vpr.LocalVarDecl("m", vpr.Int)(),vpr.LocalVarDecl("n", vpr.Int)(), vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))()),
          Seq(vpr.Trigger(Seq(vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,n,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, domainType, domainName2,vpr.NoTrafos ),m), Map.empty)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos )))()),
         vpr.Implies(vpr.NeCmp(m,n)(),vpr.EqCmp(
          
          vpr.DomainFuncApp(s"struct_loc", Seq(s,m), Map.empty)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos ) ,
                vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,n,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, domainType, domainName2,vpr.NoTrafos ),m),Map.empty)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos )
                         )()
        )())()
      )(domainName = domainName)
}
val third = {
vpr.NamedDomainAxiom(name= "axiom3", exp=vpr.Forall(Seq(vpr.LocalVarDecl("m", vpr.Int)()),Seq(vpr.Trigger(Seq(vpr.DomainFuncApp("default_tuple", Seq(vpr.LocalVarDecl("m", vpr.Int)().localVar),typeVarMapka)(vpr.NoPosition,vpr.NoInfo, domainType, domainName2,vpr.NoTrafos )))()), vpr.EqCmp(vpr.LocalVarDecl("m", vpr.Int)().localVar,vpr.DomainFuncApp("struct_lengthtup", Seq(vpr.DomainFuncApp("default_tuple", Seq(vpr.LocalVarDecl("m", vpr.Int)().localVar),typeVarMapka)(vpr.NoPosition,vpr.NoInfo, domainType, domainName2,vpr.NoTrafos ) ),typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName2,vpr.NoTrafos ))())() )(domainName = domainName)
}
    val domain3 = vpr.Domain(name="StructOps", typVars= Seq(vpr.TypeVar(s"T")), functions = Seq(struct_get, struct_rev, struct_lengthtup, default),
    axioms=Seq(first,second, third))()
    _generatedDomains ::= domain2
     _generatedDomains ::= domain3

  }
  override def typ(args: Vector[vpr.Type]): vpr.DomainType = {
    if (_generatedDomains.size== 0) {addNTuplesDomain(0);}
  
 domainType
  }
  
}
