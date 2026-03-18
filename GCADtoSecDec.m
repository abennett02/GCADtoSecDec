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
FileName: name of output file

Optional - for pre run GCAD
GcadPos: Output of positive GCAD
GcadNeg: Output of negative GCAD"

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

stream=OpenWrite[FileName];
WriteString[stream, "from pySecDec import MakePackage\n\nintegrals="<>"["];
Close[stream];

CellLoop[GcadPos, Fpoly, Upoly, Fpow, Upow, Xlist, Invs, InvsLim, FileName, False];
Print["positive integrals written to "<>FileName];

CellLoop[GcadNeg, Fpoly, Upoly, Fpow, Upow, Xlist, Invs, InvsLim,  FileName, True];

Print["negative integrals written to "<>FileName];
stream = OpenAppend[FileName];
WriteString[stream,"]"];
Close[stream];
]

RunGCADtoSecDec[Fpoly_, Upoly_, Fpow_, Upow_, Xlist_List, Invs_List, InvsLim_List, FileName_String, GcadPos_ ,GcadNeg_]:=Module[{stream, Trans, i},

Print[ToString[GcadPos//Length]<>" positive cells"];
Print[ToString[GcadNeg//Length]<>" negative cells"];

stream=OpenWrite[FileName];
WriteString[stream, "from pySecDec import MakePackage\n\nintegrals="<>"["];
Close[stream];

CellLoop[GcadPos, Fpoly, Upoly, Fpow, Upow, Xlist, Invs, InvsLim, FileName, False];
Print["positive integrals written to "<>FileName];

CellLoop[GcadNeg, Fpoly, Upoly, Fpow, Upow, Xlist, Invs, InvsLim,  FileName, True];

Print["negative integrals written to "<>FileName];
stream = OpenAppend[FileName];
WriteString[stream,"]"];
Close[stream];
]

CellLoop::usage = "Loops over each cell in a GCAD output, gets transformations, then writes to file
Inputs
-------------------
GCADoutput: Output of GCAD, split into a list for each cell
Fpoly: F polynomial
Upoly: U polynomial
Fpow: power of F polynomial
Upow: power of U polynomial
Xlist: list of Feynman parameters
Invs: list of invariants (kinematics and masses)
InvsLim: list of limits on invariants
FileName: name of output file
IsNeg: bool, True for negative cell"

CellLoop[GCADoutput_, Fpoly_, Upoly_, Fpow_, Upow_, Xlist_List, Invs_List, InvsLim_List, FileName_, IsNeg_]:=Module[{i,Cell, Trans, test, point},
For[i=1,i<((GCADoutput//Length)+1),i++,
	Print["-------------------"];
	Cell = GCADoutput[[i]];
	test = GCADoutput[[i]];
	
	Cell=Complement[Apply[List,Cell],Map[(#>0)&,Xlist],Map[(0<#)&,Xlist]];
	If[(Invs//Length)!=0,Cell=Complement[Cell,Apply[List,Reduce[InvsLim,Invs]//LogicalExpand]]];
	
	Trans=GetTrans[Cell, Xlist];
	Print[Trans];
	
	If[IsNeg,
		FormatToSecDec[Fpoly, Upoly, Fpow, Upow, Trans, Xlist, Invs, InvsLim, False,"neg"<>ToString[i],FileName, IsNeg],
		FormatToSecDec[Fpoly, Upoly, Fpow, Upow, Trans, Xlist, Invs, InvsLim, False,"pos"<>ToString[i],FileName, IsNeg]
	];
	
	point=FindInstance[InvsLim/.List->And, Invs][[1]];
	Print[Fold[ReplaceAll, test,Trans]/.point//Simplify];
];
];

GetTrans::usage="returns list of transformations from cell input
Inputs
-------------------
Cell: GCAD output cell
Xlist: list of Feynman parameters

Returns
-------------------
list of transformations"

GetTrans[Cell_,Xlist_List]:=Module[{TransList,f,i,xj,TransVar,count,pos,a,b},
TransList={};
TransVar={};

For[i=1,i<((Cell//Length)+1),i++,
	f=Cell[[i]];
	If[(Head[f]==Greater||Head[f]==Less)&&Length[f]==2,
		If[ContainsAny[{f[[1]]},Xlist],TransVar=Append[TransVar,f[[1]]],
			TransVar=Append[TransVar,f[[2]]]],
		TransVar=Append[TransVar,f[[3]]]]
	];
count=Counts[TransVar];
	
For[i=1,i<=(Xlist//Length),i++,
	pos=Position[TransVar,Xlist[[i]]];
	f=Cell[[Flatten[pos]]];
	If[Head[count[Xlist[[i]]]==Missing], Continue[]];
	If[count[Xlist[[i]]]==1,
			(*xi>...*)
		If[Head[f[[1]]]==Greater&&f[[1,1]]===Xlist[[i]]&&Length[f[[1]]]==2,
			TransList=Append[TransList,Xlist[[i]]->Xlist[[i]]+f[[1,2]]];
			Continue[]
		];
		(*xi<...*)
		If[Head[f[[1]]]==Less&&f[[1,1]]===Xlist[[i]]&&Length[f[[1]]]==2,
			TransList=Append[TransList,Xlist[[i]]->Xlist[[i]]/(Xlist[[i]]+xj)f[[1,2]]];
			Continue[]
		];
		(*...<xi*)
			If[Head[f[[1]]]==Less&&f[[1,2]]===Xlist[[i]]&&Length[f[[1]]]==2,
			TransList=Append[TransList,Xlist[[i]]->Xlist[[i]]+f[[1,1]]];
			Continue[]
		];
		(*...>xi*)
			If[Head[f[[1]]]==Greater&&f[[1,2]]===Xlist[[i]]&&Length[f[[1]]]==2,
			TransList=Append[TransList,Xlist[[i]]->Xlist[[i]]/(Xlist[[i]]+xj)f[[1,1]]];
			Continue[]
		];
		(*...<xi<...*)
		(*f1<f3<f5*)
			If[Head[f[[1]]]==Inequality&&f[[1,2]]==Less&&f[[1,3]]===Xlist[[i]],
			TransList=Append[TransList,Xlist[[i]]->(f[[1,1]]xj+f[[1,5]]Xlist[[i]])/(Xlist[[i]]+xj)];
			Continue[]
		];
		(*...>xi>...*)
		(*f5<f3<f1*)
			If[Head[f[[1]]]==Inequality&&f[[1,2]]==Greater&&f[[1,3]]===Xlist[[i]],
			TransList=Append[TransList,Xlist[[i]]->(f[[1,5]]xj+f[[1,1]]Xlist[[i]])/(Xlist[[i]]+xj)];
			Continue[]
		];
		Print["Error: "<>ToString[f]<>" not recognised"]
	,
	If[f[[1,1]]===Xlist[[i]], (*xi variable first*)
		If[Head[f[[1]]]===Greater,a=f[[1,2]],b=f[[1,2]]],
	(*xi variable second*)
		If[Head[f[[1]]]===Less,a=f[[1,1]],b=f[[1,1]]]
	];
	If[f[[2,1]]===Xlist[[i]], (*xi variable first*)
		If[Head[f[[2]]]===Greater, a=f[[2,2]], b=f[[2,2]]],
	(*xi variable second*)
		If[Head[f[[2]]]===Less, a=f[[2,1]], b=f[[2,1]]]
	];
	TransList=Append[TransList,Xlist[[i]]->(a xj + b Xlist[[i]])/(Xlist[[i]]+xj)]
	];
];
TransList=SortBy[TransList,Length[Intersection[Variables[#[[2]]],Xlist]]&];
For[i=1,i<((TransList//Length)+1),i++,
If[TransList[[i,1]]===Xlist[[1]], TransList[[i]]=(TransList[[i]])/.{xj->Xlist[[2]]}, TransList[[i]]=(TransList[[i]])/.{xj->Xlist[[1]]}]];

Reverse[TransList]
];

ApplyTrans::usage="Applies transformations to polynomial, and returns list
-------------------
Fpoly: F polynomial
Upoly: U polynomial
Fpow: power of F polynomial
Upow: power of U polynomial
TransList: list of transformations
IsNeg: bool, True for negative cell"

ApplyTrans[Fpoly_, Upoly_, Fpow_, Upow_, Xlist_List, Invs_List, InvsLim_List, Trans_List, IsNeg_]:=Module[{FpolyT,UpolyT,Jac, FpolyTN, FpolyTD, UpolyTN, UpolyTD, JacN, JacD, CombinedList,PolyList, Coeff, base, powers, point, sign},
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

point=FindInstance[(Map[(#>0)&,Xlist]/.List->And)&&(InvsLim/.List->And), Join[Invs,Xlist]][[1]];
sign = Sign[base/.point];
PolyList=Table[((sign*base)[[i]]^(powers[[i]]))//InputForm,{i,1,Length[base]}];

Coeff=Select[CombinedList,!IntersectingQ[Variables[#[[1,1]]],Xlist]&];
base=Coeff[[;;,1,1]];
powers=Map[Simplify[Total[#[[;;,2]]]]&,Coeff];

sign = Sign[base/.point];
Coeff=((Table[((base*sign)[[i]]^(powers[[i]])),{i,1,Length[Coeff]}]//Apply[Times,#]&))//InputForm;

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

FormatToSecDec[Fpoly_, Upoly_, Fpow_, Upow_, Trans_List, Xlist_List, Invs_List, InvsLim_List, IsNeg_,CellName_String,FileName_String, IsEnd_]:=Module[{FpolyT,UpolyT, Jac,polyList, coeff, stream},

{polyList,coeff}=ApplyTrans[Fpoly, Upoly, Fpow, Upow, Xlist, Invs, InvsLim, Trans, IsNeg];

stream=OpenAppend[FileName];

WriteString[stream, "MakePackage(\n"];
WriteString[stream,"name='"<>CellName<>"',\n"];
WriteString[stream,"integration_variables="];
WriteList[Xlist,stream, False];
WriteString[stream,",\npolynomials_to_decompose="];
WriteList[polyList,stream,True];
If[IsNeg, 
WriteString[stream, ",\nprefactor='gamma("<>ToString[Fpow//InputForm]<>")*exp(I*Pi*("<>ToString[Fpow//InputForm]<>"))*"<>ToString[coeff]<>"',\n"],
WriteString[stream, ",\nprefactor='gamma("<>ToString[Fpow//InputForm]<>")*"<>ToString[coeff]<>"',\n"]];
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
