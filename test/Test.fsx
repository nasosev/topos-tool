#load "../scripts/Load.fsx"
#r "nuget: FsCheck"

Test.testDeterministic ()
Test.testRandom ()
