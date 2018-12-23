Object subclass: #MyObject	instanceVariableNames: ''	classVariableNames: ''	poolDictionaries: ''	category: 'OOP3'!!MyObject methodsFor: 'partC' stamp: 'Y.B.Z 12/16/2018 13:04'!isKindOf: aClassOrInterface
	|boolFlag|
	boolFlag := false.
	(self class == aClassOrInterface or: [ self class inheritsFrom: aClassOrInterface ])
	ifTrue: [boolFlag := true].
	((self = MyObject) or: [self = MyObject class])
	ifTrue: [^boolFlag].
	(aClassOrInterface isInterface)
	ifTrue:[
		((self class behavesLike) includes: aClassOrInterface)
		ifTrue: [boolFlag := true]
		ifFalse: [boolFlag := super isKindOf: aClassOrInterface].
		(self class behavesLike) do: [ :tmpIF |
					(boolFlag)
					ifFalse:[boolFlag := tmpIF isKindOf: aClassOrInterface]
				].		
		].
	 ^boolFlag.! !"-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- "!MyObject class	instanceVariableNames: 'behavesLike isInterface'!!MyObject class methodsFor: 'generate' stamp: 'Y.B.Z 12/19/2018 13:11'!new	self isInterface	ifTrue: [AssertionFailure signal: 'Interfaces can not be instantiated!!'].
	self behavesLike do: [:tmpIF | 		(self implementsInterface: tmpIF)		 ifFalse: [AssertionFailure signal: 'Can not instantiate an Abstract class!!'].
	].
	^ self basicNew initialize! !!MyObject class methodsFor: 'interface' stamp: 'Y.B.Z 12/22/2018 11:38'!ambiguities
	|bLikeIFs ambiguitiesCollection allOfMethods|	
	bLikeIFs := self getAllBehavesLike.
	ambiguitiesCollection := Set new.
	allOfMethods := Set new.
	bLikeIFs do:
		[:tmpIF | (tmpIF interfaceGetAllMethods) do:
			[:tmpSelector | 
				(allOfMethods addNewElement: tmpSelector)
				ifFalse:[
					"causes an ambiguity"
					ambiguitiesCollection add: (tmpSelector). 
				].
			].
		].
	^(ambiguitiesCollection asSortedCollection)! !!MyObject class methodsFor: 'interface' stamp: 'compile:where: 12/7/2018 20:05'!behavesLike
	(self class = MyObject class) 
		ifTrue: [^(Set new).]
		ifFalse: [^behavesLike.].! !!MyObject class methodsFor: 'interface' stamp: 'Y.B.Z 12/19/2018 13:13'!implementsInterface: anInterface		|implements|		implements := true.		(anInterface behavesLike) do:[ :tmpIF |			tmpIF selectorsDo:[ :tmpSelector | 				(self methodIsImplemented: tmpSelector asString)				ifFalse: [implements := false.]			].].		^implements.! !!MyObject class methodsFor: 'interface' stamp: 'Y.B.Z 12/19/2018 13:10'!isImplemented
	|MyObjectSubclasses classesBehavingLikeSelf aSubclassImplementsSelf |
	(self isInterface) ifFalse: [AssertionFailure signal: self asString , ' is not an interface!!'].
	MyObjectSubclasses := MyObject allSubclasses.
	classesBehavingLikeSelf := Set new.
	MyObjectSubclasses do: [
		:subclass | (subclass isInterface)
			ifFalse:[
				((subclass behavesLike) includes: self)
				ifTrue: [classesBehavingLikeSelf add: subclass.].
			].
	].
	aSubclassImplementsSelf := classesBehavingLikeSelf collect:[:tmpSubclass | 		tmpSubclass implementsInterface: self.	].
	^(aSubclassImplementsSelf includes: true).! !!MyObject class methodsFor: 'interface' stamp: 'compile:where: 12/7/2018 20:06'!isInterface
	(self class = MyObject class) 
		ifTrue: [^false.]
		ifFalse: [^isInterface.].! !!MyObject class methodsFor: 'interface' stamp: 'compile:where: 12/18/2018 21:21'!subclass: aSubclassName 
instanceVariableNames: instVarNames 
classVariableNames: classVarNames 
poolDictionaries: poolDictionaries
category: aCategoryName
	^(self   subclass: aSubclassName 
			isInterface: false 
			behavesLike: self behavesLike
			instanceVariableNames: instVarNames 
			classVariableNames: classVarNames 
			poolDictionaries: poolDictionaries
			category: aCategoryName).! !!MyObject class methodsFor: 'interface' stamp: 'Y.B.Z 12/19/2018 22:37'!subclass: aSubclassName 
isInterface: isInterface 
behavesLike: aCollection 
instanceVariableNames: instVarNames 
classVariableNames: classVarNames 
poolDictionaries: poolDictionaries
category: aCategoryName
|newClass behavesCollection|
	isInterface 
	ifTrue:
		[((self = MyObject) or: [self = MyObject class])
			ifFalse:[AssertionFailure signal: 'Interfaces must derive from MyObject!!'].
		(instVarNames isEmpty) 
			ifFalse: [AssertionFailure signal: 'Interfaces can not have state!!'].
		]
	ifFalse:
		[ (self isInterface) 
			ifTrue: [AssertionFailure signal: 'Classes can not derive from an interface!!'].
		].
	aCollection do: [ :item |
			[(item isInterface) ifFalse:[AssertionFailure signal: 'Can not behave like a non-interface!!']]
			"in case item doesn't understand the message isInterface"
			on: Error
			do: [AssertionFailure signal: 'Can not behave like a non-interface!!'].
		].

	newClass := (ClassBuilder new)
		superclass: self
		subclass: aSubclassName
		instanceVariableNames: instVarNames
		classVariableNames: classVarNames
		poolDictionaries: poolDictionaries
		category: aCategoryName.
	(newClass)  instVarNamed: 'behavesLike' put: (Set new);
				instVarNamed: 'isInterface' put: isInterface.
	behavesCollection := self behavesLike.
	isInterface ifTrue: [behavesCollection add: newClass].
	aCollection do:[:tmpClass | behavesCollection add: tmpClass.
		(tmpClass behavesLike) do: [:x| behavesCollection add: x.].].
	(newClass)  instVarNamed: 'behavesLike' put: (behavesCollection).
	^(newClass).! !!MyObject class methodsFor: 'compiling' stamp: 'compile:where: 12/10/2018 11:39'!compile: code
	|codeToCompile|
	codeToCompile := code.
	(self isInterface)
		ifTrue:[((code withBlanksTrimmed lines size) > 1) 
			ifTrue:[AssertionFailure signal: 'Interfaces are not allowed to have methods that define behavior!!'.].
			codeToCompile := self insertEmptyMethodMarker: code.
			].

	^self compile: codeToCompile notifying: nil
	! !!MyObject class methodsFor: 'compiling' stamp: 'compile:where: 12/8/2018 22:34'!compile: aSourceCode where: anOrderedCollection
	|sourceCodeLines numOfArgs newCompileCheck newCode|
	sourceCodeLines := aSourceCode lines.
	numOfArgs := (sourceCodeLines at: 1) occurrencesOf: $:.
	(numOfArgs ~~ anOrderedCollection size) ifTrue:
		[AssertionFailure signal: 'Can not compile method, number of arguments is not equal to the number of constraints!!'].
	((aSourceCode lines size > 1) and: [self isInterface.])
		ifTrue:[AssertionFailure signal: 'Interfaces are not allowed to have methods that define behavior!!'].
	newCompileCheck := self getCompileCheck: (((sourceCodeLines at: 1 ) copyReplaceAll: ':' with: ': ') findTokens: ' ') where: anOrderedCollection.
	newCode := self insertCompileCheck: newCompileCheck toCode: sourceCodeLines.
	self compile: newCode.
! !!MyObject class methodsFor: 'compiling' stamp: 'compile:where: 12/7/2018 13:34'!getCompileCheck: selectorWithArgsArray where: anOrderedCollection
	|endL addTab compileCheck|
	endL := Character cr asString. 	addTab := Character tab asString. compileCheck := String new.
	1 to: (anOrderedCollection size)  do: 
		[:i | ((anOrderedCollection at: i ) isNil) ifFalse:[
			compileCheck := compileCheck , 
			addTab, '(', (selectorWithArgsArray at: (i*2)) , ' isKindOf: ', ((anOrderedCollection at: i ) asString ) , ') ',
			'ifFalse: [AssertionFailure signal: ''Type mismatch!! Argument ',  i asString, 
				' should be ', (anOrderedCollection at: i ) asString , '''.].' , endL.].
		].
	^compileCheck.
	! !!MyObject class methodsFor: 'compiling' stamp: 'compile:where: 12/8/2018 22:21'!insertCompileCheck: compileCheck toCode: sourceCodeLinesArray
	|i endL addTab newCode|
	endL := Character cr asString. 	addTab := Character tab asString. i := 2.
	newCode := (sourceCodeLinesArray at:1) , endL.
	((sourceCodeLinesArray size) > 1)
	ifTrue:[
		((sourceCodeLinesArray at:2) includes: $|)
			ifTrue:[newCode := newCode , addTab, (sourceCodeLinesArray at:2), endL.
					i := 3.].
	].
	newCode := newCode, compileCheck.
	i to: (sourceCodeLinesArray size) do:
			[:x | newCode := newCode, addTab, (sourceCodeLinesArray at:x), endL].
	^newCode.
! !!MyObject class methodsFor: 'auxiliary' stamp: 'Y.B.Z 12/23/2018 09:52'!getAllBehavesLike	"get all the interfaces that the class/interface behaves like them"	| count currBehavesLike tempBehavesLike |	count := (self behavesLike) size.	(count = 0) ifTrue: [^Set new].	currBehavesLike := self behavesLike.	[count > 0] whileTrue: [		count := 0.		tempBehavesLike := currBehavesLike.		tempBehavesLike do:		[:tmpIf | tmpIf behavesLike do:			[:tmpIfOfBeahvesLike | 				(currBehavesLike addNewElement: tmpIfOfBeahvesLike)				ifTrue:[					count := count + 1.				].			].		].	].	^currBehavesLike.! !!MyObject class methodsFor: 'auxiliary' stamp: 'compile:where: 12/10/2018 11:34'!insertEmptyMethodMarker: code
	|endL addTab|
	endL := Character cr asString. addTab := Character tab asString.
	^(code , endL, addTab, '"@EMPTY_METHOD@"', endL)! !!MyObject class methodsFor: 'auxiliary' stamp: 'Y.B.Z 12/22/2018 11:37'!interfaceGetAllMethods	"returns all the methods of self (which suppose to be an interface) including those it gets from interfaces it behaves like them"	| bLikeIFs allMethods |	bLikeIFs := self getAllBehavesLike.	allMethods := Set new.	bLikeIFs do:		[:tmpIF | tmpIF selectorsDo:			[:tmpSelector | 				(allMethods addNewElement: tmpSelector)				].		].	^allMethods.! !!MyObject class methodsFor: 'auxiliary' stamp: 'compile:where: 12/10/2018 11:28'!methodIsEmpty: aSourceCode
	"receives a code of a method as a string, and returns if the method is empty or not"
	^((aSourceCode findString: '@EMPTY_METHOD@') > 0)
! !!MyObject class methodsFor: 'auxiliary' stamp: 'compile:where: 12/8/2018 18:40'!methodIsImplemented: aSelector
	"receives a selector of a method (as a string!!!!!!), and returns if the method is implemented by this class (or any of it's 	super classes) or not"
	"if the selector wasn't found - returns false"
	^[((self methodIsEmpty: ((self decompile: (aSelector asSymbol)) asString)) not).]
		on: Error	"the method wasn't found in the methodDict"
		do:  [(self = MyObject class) ifTrue: [^false]
			ifFalse: [(self = MyObject) ifTrue:[^false]
				ifFalse:[	^superclass methodIsImplemented: aSelector.]
				.]
			.].
! !