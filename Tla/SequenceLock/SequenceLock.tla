---- MODULE SequenceLock ----
EXTENDS Naturals, TLC, Sequences, FiniteSets

CONSTANT Readers, Writers, ValueSize

InitialValue == [ index \in 1 .. ValueSize |-> CHOOSE writer \in ( Writers \union Readers ) : TRUE ]

(* --algorithm SequenceLock 

variables
    SequenceNumber = 0,
    Value = InitialValue;

process Reader \in Readers
variable 
    ExpectedSequenceNumber = 0,
    ReadValue = << >>;
begin

Read_InitialSequenceNumber:
    await SequenceNumber % 2 = 0;
    ExpectedSequenceNumber := SequenceNumber;
    ReadValue := << >>;

Read_Value:
    while Len(ReadValue) # ValueSize do
        ReadValue := ReadValue \o << Value[Len(ReadValue) + 1] >>
    end while;

Read_FinalSequenceNumber:
    if SequenceNumber # ExpectedSequenceNumber then
        goto Read_InitialSequenceNumber;
    else
        assert(
        \/  \E writer \in Writers : 
            \A index \in 1..Len(ReadValue) :
                ReadValue[index] = writer
        \/  ReadValue = InitialValue
        );
    end if;

end process;

process Writer \in Writers
variable
    ExpectedSequenceNumber = 0,
    WriteIndex = 1;
begin

Write_InitialSequenceNumber:
    await SequenceNumber % 2 = 0;
    ExpectedSequenceNumber := SequenceNumber;
    SequenceNumber := SequenceNumber + 1;
    WriteIndex := 1;

Write_Value:
    while WriteIndex <= ValueSize do
        Value[WriteIndex] := self;
        WriteIndex := WriteIndex + 1;
    end while;

Write_FinalSequenceNumber:
    SequenceNumber := SequenceNumber + 1;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9bb30598" /\ chksum(tla) = "3cdcb31e")
\* Process variable ExpectedSequenceNumber of process Reader at line 16 col 5 changed to ExpectedSequenceNumber_
VARIABLES SequenceNumber, Value, pc, ExpectedSequenceNumber_, ReadValue, 
          ExpectedSequenceNumber, WriteIndex

vars == << SequenceNumber, Value, pc, ExpectedSequenceNumber_, ReadValue, 
           ExpectedSequenceNumber, WriteIndex >>

ProcSet == (Readers) \cup (Writers)

Init == (* Global variables *)
        /\ SequenceNumber = 0
        /\ Value = InitialValue
        (* Process Reader *)
        /\ ExpectedSequenceNumber_ = [self \in Readers |-> 0]
        /\ ReadValue = [self \in Readers |-> << >>]
        (* Process Writer *)
        /\ ExpectedSequenceNumber = [self \in Writers |-> 0]
        /\ WriteIndex = [self \in Writers |-> 1]
        /\ pc = [self \in ProcSet |-> CASE self \in Readers -> "Read_InitialSequenceNumber"
                                        [] self \in Writers -> "Write_InitialSequenceNumber"]

Read_InitialSequenceNumber(self) == /\ pc[self] = "Read_InitialSequenceNumber"
                                    /\ SequenceNumber % 2 = 0
                                    /\ ExpectedSequenceNumber_' = [ExpectedSequenceNumber_ EXCEPT ![self] = SequenceNumber]
                                    /\ ReadValue' = [ReadValue EXCEPT ![self] = << >>]
                                    /\ pc' = [pc EXCEPT ![self] = "Read_Value"]
                                    /\ UNCHANGED << SequenceNumber, Value, 
                                                    ExpectedSequenceNumber, 
                                                    WriteIndex >>

Read_Value(self) == /\ pc[self] = "Read_Value"
                    /\ IF Len(ReadValue[self]) # ValueSize
                          THEN /\ ReadValue' = [ReadValue EXCEPT ![self] = ReadValue[self] \o << Value[Len(ReadValue[self]) + 1] >>]
                               /\ pc' = [pc EXCEPT ![self] = "Read_Value"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Read_FinalSequenceNumber"]
                               /\ UNCHANGED ReadValue
                    /\ UNCHANGED << SequenceNumber, Value, 
                                    ExpectedSequenceNumber_, 
                                    ExpectedSequenceNumber, WriteIndex >>

Read_FinalSequenceNumber(self) == /\ pc[self] = "Read_FinalSequenceNumber"
                                  /\ IF SequenceNumber # ExpectedSequenceNumber_[self]
                                        THEN /\ pc' = [pc EXCEPT ![self] = "Read_InitialSequenceNumber"]
                                        ELSE /\ Assert(      (
                                                       \/  \E writer \in Writers :
                                                           \A index \in 1..Len(ReadValue[self]) :
                                                               ReadValue[self][index] = writer
                                                       \/  ReadValue[self] = InitialValue
                                                       ), 
                                                       "Failure of assertion at line 34, column 9.")
                                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << SequenceNumber, Value, 
                                                  ExpectedSequenceNumber_, 
                                                  ReadValue, 
                                                  ExpectedSequenceNumber, 
                                                  WriteIndex >>

Reader(self) == Read_InitialSequenceNumber(self) \/ Read_Value(self)
                   \/ Read_FinalSequenceNumber(self)

Write_InitialSequenceNumber(self) == /\ pc[self] = "Write_InitialSequenceNumber"
                                     /\ SequenceNumber % 2 = 0
                                     /\ ExpectedSequenceNumber' = [ExpectedSequenceNumber EXCEPT ![self] = SequenceNumber]
                                     /\ SequenceNumber' = SequenceNumber + 1
                                     /\ WriteIndex' = [WriteIndex EXCEPT ![self] = 1]
                                     /\ pc' = [pc EXCEPT ![self] = "Write_Value"]
                                     /\ UNCHANGED << Value, 
                                                     ExpectedSequenceNumber_, 
                                                     ReadValue >>

Write_Value(self) == /\ pc[self] = "Write_Value"
                     /\ IF WriteIndex[self] <= ValueSize
                           THEN /\ Value' = [Value EXCEPT ![WriteIndex[self]] = self]
                                /\ WriteIndex' = [WriteIndex EXCEPT ![self] = WriteIndex[self] + 1]
                                /\ pc' = [pc EXCEPT ![self] = "Write_Value"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Write_FinalSequenceNumber"]
                                /\ UNCHANGED << Value, WriteIndex >>
                     /\ UNCHANGED << SequenceNumber, ExpectedSequenceNumber_, 
                                     ReadValue, ExpectedSequenceNumber >>

Write_FinalSequenceNumber(self) == /\ pc[self] = "Write_FinalSequenceNumber"
                                   /\ SequenceNumber' = SequenceNumber + 1
                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << Value, 
                                                   ExpectedSequenceNumber_, 
                                                   ReadValue, 
                                                   ExpectedSequenceNumber, 
                                                   WriteIndex >>

Writer(self) == Write_InitialSequenceNumber(self) \/ Write_Value(self)
                   \/ Write_FinalSequenceNumber(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Readers: Reader(self))
           \/ (\E self \in Writers: Writer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Invariant == SequenceNumber <= Cardinality(Writers) * 2

Symmetry == Permutations(Readers) \union Permutations(Writers)

====
