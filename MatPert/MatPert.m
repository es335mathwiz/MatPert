(* Mathematica Package *)

(* Created by the Wolfram Workbench Jun 17, 2013 *)


Print["Code requires Combinatorica package and shadows some functions Mathematica has reimplemented http://reference.wolfram.com/mathematica/Compatibility/tutorial/Combinatorica.html"]
(* Mathematica Package *)
(*Uses Java Class MultiIndex *)
Quiet[BeginPackage["MatPert`", { "JLink`", "NumericAMA`", "SymbolicAMA`"(*,"Combinatorica`"*)(*,"umbralCalculus`"*)}]]
(* Exported symbols added here with SymbolName::usage *)  



  

theIndex::usage="theIndex[beta_List]"

intOut::usage = "intOut  "

polyToMultiIndexed::usage = "polyToMultiIndexed  "

theMIsToOrder::usage = "theMIsToOrder  "

eraseMemory::usage = "eraseMemory  "

Begin["`Private`"] (* Begin Private Context *) 




theIndex[beta_List]:=index[beta];(*for export*)


index[beta_List]:=
index/:index[beta]=(*memoized*)
With[{nn=Length[beta]},
Sum[With[{sc=(Apply[Plus , Drop[beta,cc-1]])-1},
pascal[nn-cc+1,sc]],{cc,nn}]]

pascal[cc_Integer,kk_Integer]:=
pascal/:pascal[cc,kk]=(*memoized*)
	    If[kk==-1, 0,If[cc==0||kk==0,1,
	      Binomial[cc+kk,kk]]]
	  
eraseMemory[]:=(UpValues[#]={})&/@{index,pascal,theMIsToOrder,possibleLForPs}


ps[ss_Integer,nu_List,lambda_List]:=
Module[{},
With[{kRes=kForPs[ss,nu,lambda]},
With[{kVals=getKVals[kRes]},
With[{lVals=Map[getLVals[possibleLForPs[ss,nu,#]]&,kVals]},
ps/:ps[ss,nu,lambda]=(*memoized*)
Flatten[MapThread[distributeEm,{kVals,lVals}],1]]]]]/;
And[ss>0,ss<=Apply[Plus ,nu]]


distributeEm[xx_,yy_List]:=
Module[{},Map[{xx,#}&,yy]]

noneZero[lList_List]:=FreeQ[Map[theSum,lList],0]

doSelectKSum[possibleTrips_List,aKSum_List]:=
doSelectKSum/:doSelectKSum[possibleTrips,aKSum]=(*memoized*)
Select[Select[possibleTrips,
		noneZero
	],
	( (aKSum . #)) ==nu&
	]


possibleLForPs[ss_Integer,nu_List,aKVal_List]:=
Module[{},
With[{aKSum=Map[(Apply[Plus , #])&, aKVal]},
With[{dd=Length[nu],nn=Apply[Plus , nu]},
With[{possibleLs=If[dd==1,Transpose[{Range[0,nn]}],
Flatten[Apply[Outer,Join[{List},Table[Range[0,nn],{dd}]]],dd-1]]},
With[{possibleTrips=myKSubsets[possibleLs,ss]},
With[{smlSet=Select[Select[possibleTrips,
		noneZero
	],
	( (aKSum . #)) ==nu&
	]
},
possibleLForPs/:possibleLForPs[ss,nu,aKVal]=(*memoized*)
	{dd,nn,possibleLs,possibleTrips,smlSet}]]]]]]/;
And[ss>0,ss<=Apply[Plus ,nu],Length[aKVal]==ss]


getLVals[lRes_List]:=lRes[[5]]

myKSubsets[ll_List,ss_Integer]:=
myKSubsets/:myKSubsets[ll,ss]=(*memoized*)
KSubsets[ll,ss]

kForPs[ss_Integer,nu_List,lambda_List]:=
Module[{},
With[{dd=Length[nu],mm=Length[lambda],nn=Apply[Plus , nu]},
If[ss===1,
With[{kVals={{lambda}}},
With[{},
{dd,mm,nn,kVals}]],
With[{kPartsRaw=Map[Select[Compositions[#,ss],True&]& ,lambda]},
If[Length[lambda]===1,
With[{kVals=Flatten[kPartsRaw,1]/.xx_Integer->{xx}},
With[{},
{dd,mm,nn,Select[kVals,noneZero]}]],
With[{kPartsOuter=Apply[Outer , Join[{List},kPartsRaw,{1}]]},
With[{kVals=Map[Transpose ,
Flatten[kPartsOuter,mm-1]]},
With[{},
With[{},
With[{},
{dd,mm,nn,Select[kVals,noneZero]}]]]]]]]]]]/;
And[ss>0,ss<=Apply[Plus ,nu],(Apply[Plus , lambda])<=(Apply[Plus , nu])]

newPs[ss_Integer,nu_?VectorQ,lambda_?VectorQ]:=
With[{possibleKs=genKs},
	possibleKs]

genKs[ss_Integer,lambda_?VectorQ]:=
If[ss==1,{lambda},
With[{possibleComps=Compositions[#,ss]&/@lambda},
Outer[ff,#]& @possibleComps]]

getD[kRes_List]:=kRes[[1]]
getM[kRes_List]:=kRes[[2]]
getN[kRes_List]:=kRes[[3]]
getKVals[kRes_List]:=kRes[[4]]


pOrderLst1Smaller[lst1_List,lst2_List]:=
If[(Apply[Plus ,lst1]) <(Apply[Plus ,lst2]),True,
If[(Apply[Plus ,lst1]) >(Apply[Plus ,lst2]),False,
With[{diff=lst1-lst2},
With[{pp1=Flatten[Position[Map[(#<0)&,diff],True]],
pp2=Flatten[Position[Map[(#>0)&,diff],True]]},
If[pp1==={},False,If[First[pp1]<First[pp2],True,False,False]]]]]]


allLambda[mm_Integer,nn_Integer]:=Compositions[nn,mm]

aTerm[nu_?VectorQ,lambda_List,ss_Integer,{},jj_Integer,gg_?MatrixQ]:=0

aTerm[nu_?VectorQ,lambda_List,ss_Integer,ps_List,jj_Integer,gg_?MatrixQ]:=
With[{nn=Apply[Plus , nu]},
With[{kVals=ps[[1]],lVals=ps[[2]]},
doExp[doMapDrv[gg,lVals[[jj]]],kVals[[jj]]]/
(doFac[kVals[[jj]]]*((doFac[lVals[[jj]]])^theSum[kVals[[jj]]]))]]/;Length[gg]==Length[ps[[1,1]]]


overJ[nu_?VectorQ,lambda_List,ss_Integer,ps_List,gg_?MatrixQ]:=
(Apply[Times , Map[aTerm[nu,lambda,ss,ps,#,gg]&,Range[ss]]])

overPs[nu_?VectorQ,lambda_List,ss_Integer,gg_?MatrixQ]:=
With[{allPs=ps[ss,nu,lambda]},
Apply[Plus , (Map[overJ[nu,lambda,ss,#,gg]&,allPs])]]

overS[nu_?VectorQ,lambda_List,gg_?MatrixQ]:=
With[{nn=Apply[Plus , nu]},
(Apply[Plus ,(Map[overPs[nu,lambda,#,gg]&,Range[nn]])])]



polysForNu[nu_?VectorQ,gg_?MatrixQ]:=
With[{mm=Length[gg]},
	With[{allLam=theMIsToOrder[mm, Plus@@nu]},
doFac[nu]*(overS[nu,#,gg]&/@allLam)]]



lambdaSumsForGivenNu[nu_List,ff_?MatrixQ,gg_?MatrixQ]:=
With[{polys=polysForNu[nu,gg],drvsNeeded=pascal[Plus@@nu,Length[gg]]-1},
	(Plus @@ (#[[Range[drvsNeeded]]]*polys))&/@ff]/;
And[Length[gg[[1]]]>=pascal[Plus@@nu,Length[nu]]-1,Length[ff[[1]]]>=pascal[Plus@@nu,Length[gg]]-1]
	
	
lambdaSumsDiffOrder[diffOrder_Integer,gArgs_Integer,ff_?MatrixQ,gg_?MatrixQ]:=
With[{allNu=Flatten[Join[Reverse[allLambda[gArgs,#]]&/@Range[diffOrder]],1]},Transpose[lambdaSumsForGivenNu[#,ff,gg]&/@allNu]]/;
And[Length[gg[[1]]]>=pascal[diffOrder,gArgs]-1,Length[ff[[1]]]>=pascal[diffOrder,Length[gg]]-1]

lambdaSumsDiffOrder[diffOrder_Integer,gArgs_Integer,ff_?MatrixQ,gg_?MatrixQ]:=
With[{gCols=Length[gg[[1]]],gRows=Length[gg]},
	Print[StringForm["With diffOrder=`` gArgs=`` gMat should have at least `` columns and exactly `` rows. fMat should have at least `` columns",
		 diffOrder,gArgs,pascal[diffOrder,gArgs]-1,gArgs,pascal[diffOrder,Length[gg]]-1]]]

 
(*

overLambda[nu_List,ff_,gg_List]:=
With[{nn=theSum[nu],mm=Length[gg]},
doFac[nu]*(Apply[Plus , Flatten[(Map[Function[xx,Map[(doDrv[ff,#]*
overS[nu,#,ff,gg])& ,allLambda[mm,xx]]],
Range[nn]])]])]



vecFdbTermForNu[nu_List,gg_List]:=
With[{nn=theSum[nu],mm=Length[gg]},
doFac[nu]*((Map[Function[xx,Map[(overS[nu,#,ff,gg])& 
,allLambda[mm,xx]]],
Range[nn]]))]


vecFdbGMultForNu[nu_List,gg_List]:=
With[{nn=theSum[nu],mm=Length[gg]},
doFac[nu]*((Map[Function[xx,Map[(overS[nu,#,ff,gg])& 
,allLambda[mm,xx]]],
Range[1,nn]]))]




vecFdbTerm[deg_Integer,gArgs_Integer,gg_List]:=
With[{allNuVals=allLambda[gArgs,deg]},
Map[vecFdbTermForNu[#,gg]&,allNuVals]]

vecFdbGMult[deg_Integer,gArgs_Integer,gg_List]:=
With[{allNuVals=allLambda[gArgs,deg]},
With[{raw=Map[vecFdbGMultForNu[#,gg]&,allNuVals]},
MapThread[toJava,raw]]]

toJava[argPyr___]:=Reverse[Map[Reverse,Transpose[{argPyr}]]]

*)
doMapDrv[gg_?MatrixQ,lVal_List]:=Map[doDrv[#,lVal]&,gg]

doFac[nums_List]:=Apply[Times ,(Map[Factorial,nums])]

theSum[xx_List]:=Apply[Plus , xx]

doExp[bot_List,top_List]:=Module[{},
Apply[Times,
MapThread[myPower,{bot,top}]]]/;Length[bot]==Length[top]
myPower[x_,y_]:=If[x===y===0,1,Power[x,y]]


doDrv[gg_Symbol,drvs_List]:=
(Apply[Derivative,drvs])[gg][]

doDrv[gg_,drvs_List]:=With[{offset=theIndex[drvs]},gg[[offset]]]


intOut[expr_,aSoln_List,epsVar_Symbol]:=Chop[Expand[expr/.aSoln]/.{epsVar^pp_:>Symbol["Global`mom$"<>ToString[epsVar]][pp],epsVar:>0}]

intOut[expr_,aSoln_List,{}]:=expr/.aSoln

intOut[expr_,aSoln_List,epsVars_List]:=Fold[intOut[#1,Flatten[aSoln],#2]&,expr,epsVars]


intOut[expr_,aSoln_List,(epsVar_Symbol)[Global`t+lead_Integer/;lead>0]]:=Chop[Expand[expr/.aSoln]/.
	{epsVar[Global`t+lead]^pp_:>Symbol["Global`mom$"<>ToString[epsVar]][pp],epsVar[Global`t+lead]:>0}]

intOut[expr_,aSoln_List,{}]:=expr/.aSoln

intOut[expr_,aSoln_List,epsVars_List]:=Fold[intOut[#1,Flatten[aSoln],#2]&,expr,epsVars]




genTerm[vars_List,pows_List]:=(1/doFac[pows])*(Times @@ MapThread[#1^#2&,{vars,pows}])

allPows[numVars_Integer,pow_Integer]:=
With[{allFacets=Reverse[allLambda[numVars,#]]&/@Range[pow]}, Join @@ allFacets]

genAllProducts[vars_List,pow_Integer]:=With[{allP=allPows[Length[vars],pow]},
genTerm[vars,#]&/@allP]

(*varname followed by lin pt*)
genPolys[vars_?VectorQ,linPt_?NumberQ,pow_Integer,coeffs_?VectorQ]:=
With[{allP=genAllProducts[vars,pow]},linPt+Plus @@(allP*coeffs)]/;
pascal[Length[vars],pow]-1==Length[coeffs]

genPolys[vars_?VectorQ,linPts_?VectorQ,pow_Integer,coeffs_?MatrixQ]:=
MapThread[genPolys[vars,#1,pow,#2]&,{linPts,coeffs}]/;And[
	Length[linPts]==Length[coeffs],
	pascal[Length[vars],pow]-1==Length[coeffs[[1]]]]

genPolys[vars_?VectorQ,linPts_?VectorQ,pow_Integer,coeffs_?MatrixQ]:=
StringForm["Length[linPts] ``, should be the same as Length of coeffs ``. And the number of columns of  coeffs  ``, should be ``",
Length[linPts],Length[coeffs],Length[coeffs[[1]]],pascal[Length[vars],pow]-1]

polyToMultiIndexed[aPoly_]:=polyToMultiIndexed[{aPoly}]
polyToMultiIndexed[thePolys_List]:=
With[{theVarsPerm=pertOrder[Union[Flatten[DeleteCases[Variables[thePolys],_?momentQ]]]]},Print[theVarsPerm];
With[{oldRules=
		CoefficientRules[thePolys,theVarsPerm[[1]]]},	
	With[{cRules=multFac[#]&/@oldRules
		},
With[{order= Max[Plus @@ #[[1]]& /@
	Flatten[cRules,2]],numVars=Length[theVarsPerm[[1]]]},
With[{theMIs=theMIsToOrder[numVars,order]},
With[{forResult=SparseArray[{},{Length[thePolys],Length[theMIs]}],
		replacements=aRowPositionValuePair[theMIs,#]&/@cRules},
With[{repArgs=Flatten[MapIndexed[replacePairs[#1,#2[[1]]]&,replacements],1]},
		ReplacePart[forResult,repArgs]
	]]]]]]]


momentQ[var_]:=Or[MatchQ[var,Global`mom[_,_]],umbralMomQ[var]]

umbralMomQ[var_[_]]:=Not[
StringFreeQ[ToString[var], RegularExpression["^mom\$"]]]

multFac[oldRules_List]:=
(#[[1]]->(doFac[#[[1]]]*#[[2]]))&/@oldRules

pertOrder[someVars_List]:=
With[{theEpsVars=Sort[Cases[someVars,Global`eps[_][t+_.]]],
theSigma=Cases[someVars,Global`Sigma]},
With[{theRest=Sort[Complement[someVars,Join[theEpsVars,theSigma]]]},
	With[{newVarsList=	Join[theRest,theEpsVars,theSigma]},
	{newVarsList,getPermutation[someVars,newVarsList]}]]]

getPermutation[oldVars_List,newVars_List]:=
Range[Length[newVars]]


replacePairs[posValPair_?MatrixQ,theRow_Integer]:=
MapThread[{theRow,#1}->#2&,posValPair]

	
aRowPositionValuePair[theMIs_List,cRulesRow_List]:=
With[{noConstants=Select[cRulesRow,Plus@@ #[[1]]>0&]},
With[{locs=Flatten[Position[theMIs,#[[1]]]&/@
	noConstants]},
	{locs,Last/@noConstants}]]
	
theMIsToOrder[numVars_Integer,ord_Integer]:=
theMIsToOrder/:theMIsToOrder[numVars,ord]=(*memoized*)
Flatten[Join[Reverse[allLambda[numVars,#]]&/@Range[ord]],1]



End[] (* End Private Context *)

EndPackage[]

