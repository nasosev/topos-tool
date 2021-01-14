#load "../scripts/LoadCompiled.fsx"
#r "nuget: FsCheck"


Test.testDeterministic ()
Test.testRandom ()
