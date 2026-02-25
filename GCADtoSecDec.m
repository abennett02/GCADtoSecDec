(* ::Package:: *)

RunGCADtoSecDec::usage = "Runs GCAD on inputed polynomial, and writes output in pySecDec format
Inputs
-------------------
Fpoly: F polynomial
Upoly: U polynomial
Fpow: power of F polynomial
Upow: power of U polynomial
Xlist: list of Feynman parameters
Invs: list of invariants (kinematics and masses)
InvsLim: list of limits on invariants
FileName: name of output file"

RunGCADtoSecDec[Fpoly_, Upoly_, Fpow_, Upow_, Xlist_List, Invs_List, InvsLim_List, FileName_String]:=Module[{GcadArg,GcadPos,GcadNeg, stream, Trans,i},
GcadArg=(Map[(#>0)&,Xlist]/.List->And)&&(InvsLim/.List->And);
(*Running GCAD*);
(*Pos*);
GcadPos=GenericCylindricalDecomposition[Fpoly>0&&GcadArg,Join[Invs,Xlist]][[1]]//LogicalExpand;
Print["GCAD run (pos)"];
(*Neg*)
GcadNeg=GenericCylindricalDecomposition[Fpoly<0&&GcadArg,Join[Invs,Xlist]][[1]]//LogicalExpand;
Print["GCAD run (neg)"];

GcadPos=ReplaceAll[GcadPos,Or->List]//List//Flatten;
GcadNeg=ReplaceAll[GcadNeg,Or->List]//List//Flatten;
Print[ToString[GcadPos//Length]<>" positive cells"];
Print[ToString[GcadNeg//Length]<>" negative cells"];
posTest=GcadPos;
negTest=GcadNeg;

stream=OpenWrite[FileName];
WriteString[stream, "from pySecDec import MakePackage\n\nintegrals="<>"["];
Close[stream];

(*Remove original constraints from output. note: xi>0 and 0<xi are checked seperately, and invariants are reduced and expanded to hopefully match the output of GCAD.*)
For[i=1,i<((GcadPos//Length)+1),i++,
Print["-------------------"];
GcadPos[[i]]=Complement[Apply[List,GcadPos[[i]]],Map[(#>0)&,Xlist],Map[(0<#)&,Xlist]];
If[(Invs//Length)!=0,GcadPos[[i]]=Complement[GcadPos[[i]],Apply[List,Reduce[InvsLim,Invs]//LogicalExpand]]];

Trans=GetTrans[GcadPos[[i]], Xlist];

FormatToSecDec[Fpoly, Upoly, Fpow, Upow, Trans, Xlist, False,"pos"<>ToString[i],FileName, False];
Print[Fold[ReplaceAll, posTest[[i]],Trans]//Simplify];
];
Print["positive integrals written to "<>FileName];
For[i=1,i<((GcadNeg//Length)+1),i++,
Print["-------------------"];
GcadNeg[[i]]=Complement[Apply[List,GcadNeg[[i]]],Map[(#>0)&,Xlist],Map[(0<#)&,Xlist]];
If[(Invs//Length)!=0,GcadNeg[[i]]=Complement[GcadNeg[[i]],Apply[List,Reduce[InvsLim,Invs]//LogicalExpand]]];

Trans=GetTrans[GcadNeg[[i]], Xlist];

FormatToSecDec[Fpoly, Upoly, Fpow, Upow, Trans, Xlist, True,"neg"<>ToString[i],FileName,i==(GcadNeg//Length)];
Print[Fold[ReplaceAll, negTest[[i]],Trans]//Simplify];
];

stream = OpenAppend[FileName];
WriteString[stream,"]"];
Close[stream];

Print["negative integrals written to "<>FileName];
]

GetTrans::usage="returns list of transformations from cell input
Inputs
-------------------
Cell: GCAD output cell
Xlist: list of Feynman parameters

Returns
-------------------
list of transformations"

GetTrans[Cell_,Xlist_List]:=Module[{TransList,f,i},
TransList={};
(*Bug: transformations must be ordered in ascending order of complexity e.g. x1 -> f(no x1), x2 ->f(no x1,x2), (then applied in reverse to functions). Mostly, GCAD output is in correct order, but sometimes isn't - add in sorting of transformations.*)
For[i=1,i<((Cell//Length)+1),i++,
f=Cell[[i]];
(*xi>...*)
If[Head[f]==Greater&&ContainsAny[{f[[1]]},Xlist]&&Length[f]==2,
TransList=Append[TransList,f[[1]]->f[[1]]+f[[2]]];
Continue[]
];
(*xi<...*)
If[Head[f]==Less&&ContainsAny[{f[[1]]},Xlist]&&Length[f]==2,
If[f[[1]]===Xlist[[1]],xj=Xlist[[2]],xj=Xlist[[1]]];
TransList=Append[TransList,f[[1]]->f[[1]]/(f[[1]]+xj)f[[2]]];
Continue[]
];
(*...<xi*)
If[Head[f]==Less&&ContainsAny[{f[[2]]},Xlist]&&Length[f]==2,
TransList=Append[TransList,f[[2]]->f[[2]]+f[[1]]];
Continue[]
];
(*...>xi*)
If[Head[f]==Greater&&ContainsAny[{f[[2]]},Xlist]&&Length[f]==2,
If[f[[2]]===Xlist[[1]],xj=Xlist[[2]],xj=Xlist[[1]]];
TransList=Append[TransList,f[[2]]->f[[2]]/(f[[2]]+xj)f[[1]]];
Continue[]
];
(*...<xi<...*)
If[Head[f]==Inequality&&f[[2]]==Less&&ContainsAny[{f[[3]]},Xlist],
If[f[[3]]===Xlist[[1]],xj=Xlist[[2]],xj=Xlist[[1]]];
TransList=Append[TransList,f[[3]]->f[[3]]+f[[1]]];
TransList=Append[TransList,f[[3]]->f[[3]]/(f[[3]]+xj)f[[5]]];
Continue[]
];
(*...>xi>...*)
If[Head[f]==Inequality&&f[[2]]==Greater&&ContainsAny[{f[[3]]},Xlist],
If[f[[3]]===Xlist[[1]],xj=Xlist[[2]],xj=Xlist[[1]]];
TransList=Append[TransList,f[[3]]->f[[3]]/(f[[3]]+xj)f[[1]]];
TransList=Append[TransList,f[[3]]->f[[3]]+f[[5]]];
Continue[]
];
Print["Error: "<>ToString[f]<>" not recognised"]
];
TransList=SortBy[TransList,Length[Intersection[Variables[#[[2]]],Xlist]]&];
Reverse[TransList]
]

ApplyTrans::usage="Applies transformations to polynomial, and returns list
-------------------
Fpoly: F polynomial
Upoly: U polynomial
Fpow: power of F polynomial
Upow: power of U polynomial
TransList: list of transformations
IsNeg: bool, True for negative cell"

ApplyTrans[Fpoly_, Upoly_, Fpow_, Upow_, Xlist_List, Trans_List, IsNeg_]:=Module[{FpolyT,UpolyT,Jac, FpolyTN, FpolyTD, UpolyTN, UpolyTD, JacN, JacD, CombinedList,PolyList, Coeff, base, powers},
FpolyT=Fold[ReplaceAll,Fpoly,Trans]//Simplify//Together;
If[IsNeg,FpolyT=FpolyT*-1];
UpolyT=Fold[ReplaceAll,Upoly,Trans]//Simplify//Together;
Jac=Fold[(#1/.#2)*D[#2[[2]],#2[[1]]]&,1,Trans]//Simplify//Together;

FpolyTN=FpolyT//Numerator//FactorList;
FpolyTN[[;;,2]]=FpolyTN[[;;,2]]*(-Fpow);

FpolyTD=FpolyT//Denominator//FactorList;
FpolyTD[[;;,2]]=FpolyTD[[;;,2]]*(Fpow);

UpolyTN=UpolyT//Numerator//FactorList;
UpolyTN[[;;,2]]=UpolyTN[[;;,2]]*(Upow);

UpolyTD=UpolyT//Denominator//FactorList;
UpolyTD[[;;,2]]=UpolyTD[[;;,2]]*(-Upow);

JacN=Jac//Numerator//FactorList;

JacD=Jac//Denominator//FactorList;
JacD[[;;,2]]=JacD[[;;,2]]*(-1);

CombinedList=GatherBy[{FpolyTN,FpolyTD,UpolyTN,UpolyTD,JacN,JacD}//Flatten[#,1]&,#[[1]]&];

PolyList=Select[CombinedList,IntersectingQ[Variables[#[[1,1]]],Xlist]&];
base=PolyList[[;;,1,1]];
powers=Map[Simplify[Total[#[[;;,2]]]]&,PolyList];
PolyList=Table[(base[[i]]^(powers[[i]]))//InputForm,{i,1,Length[PolyList]}];

Coeff=Select[CombinedList,!IntersectingQ[Variables[#[[1,1]]],Xlist]&];
base=Coeff[[;;,1,1]];
powers=Map[Simplify[Total[#[[;;,2]]]]&,Coeff];
Coeff=Table[(base[[i]]^(powers[[i]])),{i,1,Length[Coeff]}]//Apply[Times,#]&//InputForm;

PolyList=Complement[PolyList,{InputForm[1]}];
{PolyList, Coeff}
];

FormatToSecDec::usage="Applies transformations to polynomial, and appends a pySecDec MakePackage() object to file
Inputs
-------------------
Fpoly: F polynomial
Upoly: U polynomial
Fpow: power of F polynomial
Upow: power of U polynomial
TransList: list of transformations
Xlist: list of Feynman parameters
IsNeg: bool, True for negative cell
CellName: name identifier for cell
FileName: name of output file
IsEnd: bool, True if object is the last to be written to file"

FormatToSecDec[Fpoly_, Upoly_, Fpow_, Upow_, Trans_List, Xlist_List, IsNeg_,CellName_String,FileName_String, IsEnd_]:=Module[{FpolyT,UpolyT, Jac,polyList, coeff, stream},

{polyList,coeff}=ApplyTrans[Fpoly, Upoly, Fpow, Upow, Xlist, Trans, IsNeg];

stream=OpenAppend[FileName];

WriteString[stream, "MakePackage(\n"];
WriteString[stream,"name='"<>CellName<>"',\n"];
WriteString[stream,"integration_variables="];
WriteList[Xlist,stream, False];
WriteString[stream,",\npolynomials_to_decompose="];
WriteList[polyList,stream,True];
If[IsNeg, 
WriteString[stream, ",\nprefactor='gamma("<>ToString[Fpow]<>")*exp(I*Pi*("<>ToString[Fpow]<>"))*"<>ToString[coeff]<>"',\n"],
WriteString[stream, ",\nprefactor='gamma("<>ToString[Fpow]<>")*"<>ToString[coeff]<>"',\n"]];
WriteString[stream, "decomposition_method='geometric'\n)"];
If[!IsEnd, WriteString[stream, ","]];
WriteString[stream,"\n\n"];
Close[stream];
]

WriteList::usage="Writes list to stream as a list of strings e.g. {a,b,c,d} written as ['a','b','c','d']
Inputs
-------------------
list: input list
stream: OutputStream
IsMline: bool, 
"
WriteList[list_List,stream_OutputStream,IsMLine_]:=Module[{i},
WriteString[stream,"["];
For[i=1, i<Length[list],i++,
WriteString[stream,"'"<> ToString[list[[i]]]<>"'"<> "," ];
If[IsMLine, WriteString[stream,"\n"]]
];
WriteString[stream,"'"<> ToString[list[[i]]]<>"'"<> "]"];
]
