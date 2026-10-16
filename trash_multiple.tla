--------------------------- MODULE trash_multiple ---------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bins
  outerDoorOpen = [b \in Bins |-> FALSE],
  outerDoorLocked = [b \in Bins |-> TRUE],
  trapDoorOpen = [b \in Bins |-> FALSE],
  ramExtended = [b \in Bins |-> FALSE],
  trashInTop = [b \in Bins |-> 0],
  trashCompressed = [b \in Bins |-> 0],
  trashUncompressed = [b \in Bins |-> 0],
  trashCapacity = [b \in Bins |-> MaxCapacity],
  trapDestroyed = [b \in Bins |-> FALSE],

  \* Variables for users
  userTrash = [u \in Users |-> 0],

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]],
  \* Sensor from outer door of bin
  binSensor = [b \in Bins |-> [sensor |-> "idle"]],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = [u \in Users |-> << >>],
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Commands for the trucks
  truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]];

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]
\* Trucks currently idle
AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}

\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.
\* Make sure your formalisations hold for every bin/user, not just one specific instance.

\* For each bin, the outer door can only be locked if it is closed.
OuterDoorLocked == \A b \in Bins : outerDoorLocked[b] => ~outerDoorOpen[b]

\* For each bin, the ram is only extended when the outer door is closed and locked.
RamOuterDoor == \A b \in Bins : ramExtended[b] => (outerDoorLocked[b] /\ ~outerDoorOpen[b])

\* For each bin, every time it is full, it is eventually not full anymore.
Full(b) == MaxCapacity - Trash(b) < MaxUserTrash
TrashEmptied == \A b \in Bins : [](Full(b) => <>~Full(b))

\* Each user infinitely often has trash and infinitely often has none.
UserTrash == \A u \in Users : ([]<>(userTrash[u] > 0)) /\ ([]<>(userTrash[u] = 0))

\* For each user, every time they have trash, they eventually deposit it.
UserTrashDeposited == \A u \in Users : [](userTrash[u] > 0 => <>(userTrash[u] = 0))

\* For each bin, every time a truck is requested for it, it is eventually emptied.
TruckEmpties == \A b \in Bins : \A t \in Trucks : [](  (truckCommand[t].command = "request" /\ truckCommand[t].bin = b) => <>(truckCommand[t].command = "emptied" /\ truckCommand[t].bin = b))


end define;


\*****************************
\* Helper macros
\*****************************

\* Compress trash
macro compress(compressed, uncompressed) begin
  compressed := compressed + IF (uncompressed > 1) THEN uncompressed \div 2 ELSE uncompressed;
  uncompressed := 0;
end macro

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro


\*****************************
\* Process for a bin
\*****************************
fair process binProcess \in Bins
begin
  BinWaitForCommand:
    while TRUE do
      await binCommand[self].command /= "finished";
      if binCommand[self].command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked[self];
        outerDoorOpen[self] := binCommand[self].open;
        if ~outerDoorOpen[self] then
          binSensor[self] := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand[self].command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen[self];
        outerDoorLocked[self] := ~(binCommand[self].open);
      elsif binCommand[self].command = "change_trap_door" then
        assert outerDoorLocked[self];
        \* Open/Close trap door
        if ramExtended[self] \/ CapacityExceeded(self) then
            trapDestroyed[self] := TRUE;
        end if;
        trapDoorOpen[self] := binCommand[self].open;
        if trapDoorOpen[self] then
          \* Trash falls through
          trashUncompressed[self] := trashUncompressed[self] + trashInTop[self];
          trashInTop[self] := 0;
        end if
      elsif binCommand[self].command = "change_ram" then
        assert outerDoorLocked[self];
        \* Extend/Retract ram
        ramExtended[self] := binCommand[self].open;
        if ramExtended[self] then
          if ~trapDoorOpen[self] then
            trapDestroyed[self] := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed[self], trashUncompressed[self]);
        end if;
      elsif binCommand[self].command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked[self];
        assert ~trapDoorOpen[self];
        assert ~ramExtended[self];
        assert trashInTop[self] = 0;
        assert trashUncompressed[self] = 0;
        trashCompressed[self] := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand[self].command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE],
  selectedBin = 0
begin
  UserNextIteration:
    while TRUE do
      if userTrash[self] = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash[self] := amt;
        end with;
      end if;
  UserScanCard:
      \* Non-deterministically choose a bin
      with sBin \in Bins do
        selectedBin := sBin;
        write(scans, [user |-> self, bin |-> selectedBin]);
      end with;
  UserAwaitScanResponse:
      read(permissions[self], perm);
      assert perm.user = self;
      assert perm.bin = selectedBin;
      if perm.granted then
  UserOpenDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand[selectedBin].command = "finished";
  UserDepositTrash:
        assert trashInTop[selectedBin] = 0;
        trashInTop[selectedBin] := userTrash[self];
        userTrash[self] := 0;
  UserCloseDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand[selectedBin].command = "finished";
      end if;
    end while;
end process;


\*****************************
\* Process for a server
\*****************************
fair process serverProcess = Server
variables
  req = [user |-> 0]
begin
  ServerNextIteration:
    while TRUE do
  ServerAwaitRequest:
      read(serverRequests, req);
      with valid \in ValidCard(req.user) do
        write(serverResponses, [user |-> req.user, permission |-> valid]);
      end with;
    end while;
end process;


\*****************************
\* Process for a truck
\*****************************
\* DUMMY truck process type.
\* Remodel it to react to requests and empty the requested trash bin!
fair process truckProcess \in Trucks
variables tb = <<>>
begin
  TruckStart:
    while TRUE do
  TruckAwaitRequest:
      await truckCommand[self].command = "request";
      tb := Append(tb, truckCommand[self].bin);
      truckCommand[self].command := "arrived";
  TruckSendEmpty:
      await binCommand[Head(tb)].command = "finished";
      binCommand[Head(tb)] := [command |-> "empty", open |-> FALSE];
      truckCommand[self].command := "start_emptying";
  TruckAwaitEmptied:
      await binCommand[Head(tb)].command = "finished";
      truckCommand[self] := [command |-> "emptied", bin |-> Head(tb)];
      tb := Tail(tb);
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
\* DUMMY main control process type.
\* Remodel it to control all trash bins in the system and handle requests by users!
fair process controlProcess = Control
variables
  scan = [user |-> 0, bin |-> 0],
  permission = [user |-> 0, bin |-> 1, granted |-> FALSE],
  thebin = 0,
  freetruck = 0
begin
  ControlStart:
   while TRUE do
   
   
    WaitScan:
     read(scans,scan);
     thebin:=scan.bin;
     if (\E t \in Trucks : (truckCommand[t].command # "emptied" /\ truckCommand[t].bin = thebin)) then 
        NoPermission:
           write(permissions[permission.user],[user |-> permission.user, bin |-> thebin, granted |-> FALSE]);
     else 
        ControlAwaitRequest:
           write(serverRequests, [user |-> scan.user, bin |-> thebin]);
        ControlAwaitResponse:
           read(serverResponses, permission);
           if permission.permission then
             ConrtolUnlockDoor:
                binCommand[thebin] := [command |-> "change_outer_lock", open |-> TRUE];
             ControlAwaitUnlockDoor:
                await binCommand[thebin].command = "finished";
             ControlGivePermission:
                write(permissions[permission.user], [user |-> permission.user, bin |-> thebin, granted |-> TRUE]);
             ControlLockOuterDoor:
                await ~outerDoorOpen[thebin] /\ trashInTop[thebin] > 0 /\ binCommand[thebin].command = "finished";
                binCommand[thebin] := [command |-> "change_outer_lock", open |-> FALSE];
             AwaitLockDoor:
                await binCommand[thebin].command = "finished";
             OpenTrapDoor:
                binCommand[thebin] := [command |-> "change_trap_door", open |-> TRUE];
             AwaitOpenTrapDoor:
                await binCommand[thebin].command = "finished";
             CloseTrapDoor:
                binCommand[thebin] := [command |-> "change_trap_door", open |-> FALSE];
             AwaitCloseTrapDoor:
                await binCommand[thebin].command = "finished";
             ExtendRam:
                binCommand[thebin] := [command |-> "change_ram", open |-> TRUE];
             AwaitExtendRam:
                await binCommand[thebin].command = "finished";
             UnExtendRam:
                binCommand[thebin] := [command |-> "change_ram", open |-> FALSE];
             AwaitUnExtendRam:
                await binCommand[thebin].command = "finished";
                
             CheckFull:
                 if Trash(thebin)  -  MaxCapacity <= MaxUserTrash then 
                  ControlerCheckTruck:
                     await AvailableTrucks /= {};
                     freetruck := CHOOSE t \in AvailableTrucks : TRUE;
                     truckCommand[freetruck] := [command |-> "request", bin |-> thebin];
                 end if;
                 
           else 
                write(permissions, [user |-> permission.user, bin |-> thebin, granted |-> FALSE]);
           end if;
      end if;
      Fix:
        thebin:=0;
    end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a98ab56b" /\ chksum(tla) = "93398d1b")
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, binCommand, binSensor, scans, permissions, 
          serverRequests, serverResponses, truckCommand, pc

(* define statement *)
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]

AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}





TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins


MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)









OuterDoorLocked == \A b \in Bins : outerDoorLocked[b] => ~outerDoorOpen[b]


RamOuterDoor == \A b \in Bins : ramExtended[b] => (outerDoorLocked[b] /\ ~outerDoorOpen[b])


Full(b) == MaxCapacity - Trash(b) < MaxUserTrash
TrashEmptied == \A b \in Bins : [](Full(b) => <>~Full(b))


UserTrash == \A u \in Users : ([]<>(userTrash[u] > 0)) /\ ([]<>(userTrash[u] = 0))


UserTrashDeposited == \A u \in Users : [](userTrash[u] > 0 => <>(userTrash[u] = 0))


TruckEmpties == \A b \in Bins : \A t \in Trucks : [](  (truckCommand[t].command = "request" /\ truckCommand[t].bin = b) => <>(truckCommand[t].command = "emptied" /\ truckCommand[t].bin = b))

VARIABLES perm, selectedBin, req, tb, scan, permission, thebin, freetruck

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, binCommand, binSensor, scans, 
           permissions, serverRequests, serverResponses, truckCommand, pc, 
           perm, selectedBin, req, tb, scan, permission, thebin, freetruck >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = [b \in Bins |-> FALSE]
        /\ outerDoorLocked = [b \in Bins |-> TRUE]
        /\ trapDoorOpen = [b \in Bins |-> FALSE]
        /\ ramExtended = [b \in Bins |-> FALSE]
        /\ trashInTop = [b \in Bins |-> 0]
        /\ trashCompressed = [b \in Bins |-> 0]
        /\ trashUncompressed = [b \in Bins |-> 0]
        /\ trashCapacity = [b \in Bins |-> MaxCapacity]
        /\ trapDestroyed = [b \in Bins |-> FALSE]
        /\ userTrash = [u \in Users |-> 0]
        /\ binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]]
        /\ binSensor = [b \in Bins |-> [sensor |-> "idle"]]
        /\ scans = << >>
        /\ permissions = [u \in Users |-> << >>]
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        /\ selectedBin = [self \in Users |-> 0]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process truckProcess *)
        /\ tb = [self \in Trucks |-> <<>>]
        (* Process controlProcess *)
        /\ scan = [user |-> 0, bin |-> 0]
        /\ permission = [user |-> 0, bin |-> 1, granted |-> FALSE]
        /\ thebin = 0
        /\ freetruck = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckStart"
                                        [] self = Control -> "ControlStart"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand[self].command /= "finished"
                           /\ IF binCommand[self].command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked[self], 
                                                "Failure of assertion at line 174, column 9.")
                                      /\ outerDoorOpen' = [outerDoorOpen EXCEPT ![self] = binCommand[self].open]
                                      /\ IF ~outerDoorOpen'[self]
                                            THEN /\ binSensor' = [binSensor EXCEPT ![self] = [sensor |-> "outer_door_closed"]]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand[self].command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen[self], 
                                                           "Failure of assertion at line 181, column 9.")
                                                 /\ outerDoorLocked' = [outerDoorLocked EXCEPT ![self] = ~(binCommand[self].open)]
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand[self].command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked[self], 
                                                                      "Failure of assertion at line 184, column 9.")
                                                            /\ IF ramExtended[self] \/ CapacityExceeded(self)
                                                                  THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = [trapDoorOpen EXCEPT ![self] = binCommand[self].open]
                                                            /\ IF trapDoorOpen'[self]
                                                                  THEN /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = trashUncompressed[self] + trashInTop[self]]
                                                                       /\ trashInTop' = [trashInTop EXCEPT ![self] = 0]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand[self].command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked[self], 
                                                                                 "Failure of assertion at line 196, column 9.")
                                                                       /\ ramExtended' = [ramExtended EXCEPT ![self] = binCommand[self].open]
                                                                       /\ IF ramExtended'[self]
                                                                             THEN /\ IF ~trapDoorOpen[self]
                                                                                        THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = (trashCompressed[self]) + IF ((trashUncompressed[self]) > 1) THEN (trashUncompressed[self]) \div 2 ELSE (trashUncompressed[self])]
                                                                                  /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand[self].command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked[self], 
                                                                                            "Failure of assertion at line 208, column 9.")
                                                                                  /\ Assert(~trapDoorOpen[self], 
                                                                                            "Failure of assertion at line 209, column 9.")
                                                                                  /\ Assert(~ramExtended[self], 
                                                                                            "Failure of assertion at line 210, column 9.")
                                                                                  /\ Assert(trashInTop[self] = 0, 
                                                                                            "Failure of assertion at line 211, column 9.")
                                                                                  /\ Assert(trashUncompressed[self] = 0, 
                                                                                            "Failure of assertion at line 212, column 9.")
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 216, column 9.")
                                                                                  /\ UNCHANGED trashCompressed
                                                                       /\ UNCHANGED << ramExtended, 
                                                                                       trashUncompressed, 
                                                                                       trapDestroyed >>
                                                            /\ UNCHANGED << trapDoorOpen, 
                                                                            trashInTop >>
                                                 /\ UNCHANGED outerDoorLocked
                                      /\ UNCHANGED << outerDoorOpen, binSensor >>
                           /\ pc' = [pc EXCEPT ![self] = "BinCommandFinished"]
                           /\ UNCHANGED << trashCapacity, userTrash, 
                                           binCommand, scans, permissions, 
                                           serverRequests, serverResponses, 
                                           truckCommand, perm, selectedBin, 
                                           req, tb, scan, permission, thebin, 
                                           freetruck >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT ![self].command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            truckCommand, perm, selectedBin, 
                                            req, tb, scan, permission, thebin, 
                                            freetruck >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash[self] = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           selectedBin, req, tb, scan, 
                                           permission, thebin, freetruck >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ \E sBin \in Bins:
                           /\ selectedBin' = [selectedBin EXCEPT ![self] = sBin]
                           /\ scans' = Append(scans, ([user |-> self, bin |-> selectedBin'[self]]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, tb, scan, 
                                      permission, thebin, freetruck >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 248, column 7.")
                               /\ Assert(perm'[self].bin = selectedBin[self], 
                                         "Failure of assertion at line 249, column 7.")
                               /\ IF perm'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               userTrash, binCommand, 
                                               binSensor, scans, 
                                               serverRequests, serverResponses, 
                                               truckCommand, selectedBin, req, 
                                               tb, scan, permission, thebin, 
                                               freetruck >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> TRUE]]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, selectedBin, req, tb, 
                                      scan, permission, thebin, freetruck >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand[selectedBin[self]].command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           selectedBin, req, tb, scan, 
                                           permission, thebin, freetruck >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop[selectedBin[self]] = 0, 
                                    "Failure of assertion at line 256, column 9.")
                          /\ trashInTop' = [trashInTop EXCEPT ![selectedBin[self]] = userTrash[self]]
                          /\ userTrash' = [userTrash EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, scans, 
                                          permissions, serverRequests, 
                                          serverResponses, truckCommand, perm, 
                                          selectedBin, req, tb, scan, 
                                          permission, thebin, freetruck >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> FALSE]]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, selectedBin, req, 
                                       tb, scan, permission, thebin, freetruck >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand[selectedBin[self]].command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, scans, 
                                             permissions, serverRequests, 
                                             serverResponses, truckCommand, 
                                             perm, selectedBin, req, tb, scan, 
                                             permission, thebin, freetruck >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = [userTrash EXCEPT ![self] = amt]
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, selectedBin, req, tb, 
                                      scan, permission, thebin, freetruck >>

userProcess(self) == UserNextIteration(self) \/ UserScanCard(self)
                        \/ UserAwaitScanResponse(self)
                        \/ UserOpenDoor(self) \/ UserAwaitOpenDoor(self)
                        \/ UserDepositTrash(self) \/ UserCloseDoor(self)
                        \/ UserAwaitClosedDoor(self) \/ UserNewTrash(self)

ServerNextIteration == /\ pc[Server] = "ServerNextIteration"
                       /\ pc' = [pc EXCEPT ![Server] = "ServerAwaitRequest"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       selectedBin, req, tb, scan, permission, 
                                       thebin, freetruck >>

ServerAwaitRequest == /\ pc[Server] = "ServerAwaitRequest"
                      /\ serverRequests /= <<>>
                      /\ req' = Head(serverRequests)
                      /\ serverRequests' = Tail(serverRequests)
                      /\ \E valid \in ValidCard(req'.user):
                           serverResponses' = Append(serverResponses, ([user |-> req'.user, permission |-> valid]))
                      /\ pc' = [pc EXCEPT ![Server] = "ServerNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, truckCommand, perm, 
                                      selectedBin, tb, scan, permission, 
                                      thebin, freetruck >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckStart(self) == /\ pc[self] = "TruckStart"
                    /\ pc' = [pc EXCEPT ![self] = "TruckAwaitRequest"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, selectedBin, req, tb, 
                                    scan, permission, thebin, freetruck >>

TruckAwaitRequest(self) == /\ pc[self] = "TruckAwaitRequest"
                           /\ truckCommand[self].command = "request"
                           /\ tb' = [tb EXCEPT ![self] = Append(tb[self], truckCommand[self].bin)]
                           /\ truckCommand' = [truckCommand EXCEPT ![self].command = "arrived"]
                           /\ pc' = [pc EXCEPT ![self] = "TruckSendEmpty"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, perm, selectedBin, 
                                           req, scan, permission, thebin, 
                                           freetruck >>

TruckSendEmpty(self) == /\ pc[self] = "TruckSendEmpty"
                        /\ binCommand[Head(tb[self])].command = "finished"
                        /\ binCommand' = [binCommand EXCEPT ![Head(tb[self])] = [command |-> "empty", open |-> FALSE]]
                        /\ truckCommand' = [truckCommand EXCEPT ![self].command = "start_emptying"]
                        /\ pc' = [pc EXCEPT ![self] = "TruckAwaitEmptied"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binSensor, scans, 
                                        permissions, serverRequests, 
                                        serverResponses, perm, selectedBin, 
                                        req, tb, scan, permission, thebin, 
                                        freetruck >>

TruckAwaitEmptied(self) == /\ pc[self] = "TruckAwaitEmptied"
                           /\ binCommand[Head(tb[self])].command = "finished"
                           /\ truckCommand' = [truckCommand EXCEPT ![self] = [command |-> "emptied", bin |-> Head(tb[self])]]
                           /\ tb' = [tb EXCEPT ![self] = Tail(tb[self])]
                           /\ pc' = [pc EXCEPT ![self] = "TruckStart"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, perm, selectedBin, 
                                           req, scan, permission, thebin, 
                                           freetruck >>

truckProcess(self) == TruckStart(self) \/ TruckAwaitRequest(self)
                         \/ TruckSendEmpty(self) \/ TruckAwaitEmptied(self)

ControlStart == /\ pc[Control] = "ControlStart"
                /\ pc' = [pc EXCEPT ![Control] = "WaitScan"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, permissions, serverRequests, 
                                serverResponses, truckCommand, perm, 
                                selectedBin, req, tb, scan, permission, thebin, 
                                freetruck >>

WaitScan == /\ pc[Control] = "WaitScan"
            /\ scans /= <<>>
            /\ scan' = Head(scans)
            /\ scans' = Tail(scans)
            /\ thebin' = scan'.bin
            /\ IF (\E t \in Trucks : (truckCommand[t].command # "emptied" /\ truckCommand[t].bin = thebin'))
                  THEN /\ pc' = [pc EXCEPT ![Control] = "NoPermission"]
                  ELSE /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitRequest"]
            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                            ramExtended, trashInTop, trashCompressed, 
                            trashUncompressed, trashCapacity, trapDestroyed, 
                            userTrash, binCommand, binSensor, permissions, 
                            serverRequests, serverResponses, truckCommand, 
                            perm, selectedBin, req, tb, permission, freetruck >>

NoPermission == /\ pc[Control] = "NoPermission"
                /\ permissions' = [permissions EXCEPT ![permission.user] = Append((permissions[permission.user]), ([user |-> permission.user, bin |-> thebin, granted |-> FALSE]))]
                /\ pc' = [pc EXCEPT ![Control] = "Fix"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, serverRequests, 
                                serverResponses, truckCommand, perm, 
                                selectedBin, req, tb, scan, permission, thebin, 
                                freetruck >>

ControlAwaitRequest == /\ pc[Control] = "ControlAwaitRequest"
                       /\ serverRequests' = Append(serverRequests, ([user |-> scan.user, bin |-> thebin]))
                       /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitResponse"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, scans, 
                                       permissions, serverResponses, 
                                       truckCommand, perm, selectedBin, req, 
                                       tb, scan, permission, thebin, freetruck >>

ControlAwaitResponse == /\ pc[Control] = "ControlAwaitResponse"
                        /\ serverResponses /= <<>>
                        /\ permission' = Head(serverResponses)
                        /\ serverResponses' = Tail(serverResponses)
                        /\ IF permission'.permission
                              THEN /\ pc' = [pc EXCEPT ![Control] = "ConrtolUnlockDoor"]
                                   /\ UNCHANGED permissions
                              ELSE /\ permissions' = Append(permissions, ([user |-> permission'.user, bin |-> thebin, granted |-> FALSE]))
                                   /\ pc' = [pc EXCEPT ![Control] = "Fix"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binCommand, binSensor, 
                                        scans, serverRequests, truckCommand, 
                                        perm, selectedBin, req, tb, scan, 
                                        thebin, freetruck >>

ConrtolUnlockDoor == /\ pc[Control] = "ConrtolUnlockDoor"
                     /\ binCommand' = [binCommand EXCEPT ![thebin] = [command |-> "change_outer_lock", open |-> TRUE]]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitUnlockDoor"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, perm, selectedBin, req, tb, 
                                     scan, permission, thebin, freetruck >>

ControlAwaitUnlockDoor == /\ pc[Control] = "ControlAwaitUnlockDoor"
                          /\ binCommand[thebin].command = "finished"
                          /\ pc' = [pc EXCEPT ![Control] = "ControlGivePermission"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashInTop, trashCompressed, 
                                          trashUncompressed, trashCapacity, 
                                          trapDestroyed, userTrash, binCommand, 
                                          binSensor, scans, permissions, 
                                          serverRequests, serverResponses, 
                                          truckCommand, perm, selectedBin, req, 
                                          tb, scan, permission, thebin, 
                                          freetruck >>

ControlGivePermission == /\ pc[Control] = "ControlGivePermission"
                         /\ permissions' = [permissions EXCEPT ![permission.user] = Append((permissions[permission.user]), ([user |-> permission.user, bin |-> thebin, granted |-> TRUE]))]
                         /\ pc' = [pc EXCEPT ![Control] = "ControlLockOuterDoor"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userTrash, binCommand, binSensor, 
                                         scans, serverRequests, 
                                         serverResponses, truckCommand, perm, 
                                         selectedBin, req, tb, scan, 
                                         permission, thebin, freetruck >>

ControlLockOuterDoor == /\ pc[Control] = "ControlLockOuterDoor"
                        /\ ~outerDoorOpen[thebin] /\ trashInTop[thebin] > 0 /\ binCommand[thebin].command = "finished"
                        /\ binCommand' = [binCommand EXCEPT ![thebin] = [command |-> "change_outer_lock", open |-> FALSE]]
                        /\ pc' = [pc EXCEPT ![Control] = "AwaitLockDoor"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binSensor, scans, 
                                        permissions, serverRequests, 
                                        serverResponses, truckCommand, perm, 
                                        selectedBin, req, tb, scan, permission, 
                                        thebin, freetruck >>

AwaitLockDoor == /\ pc[Control] = "AwaitLockDoor"
                 /\ binCommand[thebin].command = "finished"
                 /\ pc' = [pc EXCEPT ![Control] = "OpenTrapDoor"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binCommand, 
                                 binSensor, scans, permissions, serverRequests, 
                                 serverResponses, truckCommand, perm, 
                                 selectedBin, req, tb, scan, permission, 
                                 thebin, freetruck >>

OpenTrapDoor == /\ pc[Control] = "OpenTrapDoor"
                /\ binCommand' = [binCommand EXCEPT ![thebin] = [command |-> "change_trap_door", open |-> TRUE]]
                /\ pc' = [pc EXCEPT ![Control] = "AwaitOpenTrapDoor"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binSensor, scans, 
                                permissions, serverRequests, serverResponses, 
                                truckCommand, perm, selectedBin, req, tb, scan, 
                                permission, thebin, freetruck >>

AwaitOpenTrapDoor == /\ pc[Control] = "AwaitOpenTrapDoor"
                     /\ binCommand[thebin].command = "finished"
                     /\ pc' = [pc EXCEPT ![Control] = "CloseTrapDoor"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, perm, selectedBin, req, tb, 
                                     scan, permission, thebin, freetruck >>

CloseTrapDoor == /\ pc[Control] = "CloseTrapDoor"
                 /\ binCommand' = [binCommand EXCEPT ![thebin] = [command |-> "change_trap_door", open |-> FALSE]]
                 /\ pc' = [pc EXCEPT ![Control] = "AwaitCloseTrapDoor"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binSensor, scans, 
                                 permissions, serverRequests, serverResponses, 
                                 truckCommand, perm, selectedBin, req, tb, 
                                 scan, permission, thebin, freetruck >>

AwaitCloseTrapDoor == /\ pc[Control] = "AwaitCloseTrapDoor"
                      /\ binCommand[thebin].command = "finished"
                      /\ pc' = [pc EXCEPT ![Control] = "ExtendRam"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, 
                                      selectedBin, req, tb, scan, permission, 
                                      thebin, freetruck >>

ExtendRam == /\ pc[Control] = "ExtendRam"
             /\ binCommand' = [binCommand EXCEPT ![thebin] = [command |-> "change_ram", open |-> TRUE]]
             /\ pc' = [pc EXCEPT ![Control] = "AwaitExtendRam"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binSensor, scans, permissions, 
                             serverRequests, serverResponses, truckCommand, 
                             perm, selectedBin, req, tb, scan, permission, 
                             thebin, freetruck >>

AwaitExtendRam == /\ pc[Control] = "AwaitExtendRam"
                  /\ binCommand[thebin].command = "finished"
                  /\ pc' = [pc EXCEPT ![Control] = "UnExtendRam"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, userTrash, binCommand, 
                                  binSensor, scans, permissions, 
                                  serverRequests, serverResponses, 
                                  truckCommand, perm, selectedBin, req, tb, 
                                  scan, permission, thebin, freetruck >>

UnExtendRam == /\ pc[Control] = "UnExtendRam"
               /\ binCommand' = [binCommand EXCEPT ![thebin] = [command |-> "change_ram", open |-> FALSE]]
               /\ pc' = [pc EXCEPT ![Control] = "AwaitUnExtendRam"]
               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                               ramExtended, trashInTop, trashCompressed, 
                               trashUncompressed, trashCapacity, trapDestroyed, 
                               userTrash, binSensor, scans, permissions, 
                               serverRequests, serverResponses, truckCommand, 
                               perm, selectedBin, req, tb, scan, permission, 
                               thebin, freetruck >>

AwaitUnExtendRam == /\ pc[Control] = "AwaitUnExtendRam"
                    /\ binCommand[thebin].command = "finished"
                    /\ pc' = [pc EXCEPT ![Control] = "CheckFull"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, selectedBin, req, tb, 
                                    scan, permission, thebin, freetruck >>

CheckFull == /\ pc[Control] = "CheckFull"
             /\ IF Trash(thebin)  -  MaxCapacity <= MaxUserTrash
                   THEN /\ pc' = [pc EXCEPT ![Control] = "ControlerCheckTruck"]
                   ELSE /\ pc' = [pc EXCEPT ![Control] = "Fix"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binCommand, binSensor, scans, 
                             permissions, serverRequests, serverResponses, 
                             truckCommand, perm, selectedBin, req, tb, scan, 
                             permission, thebin, freetruck >>

ControlerCheckTruck == /\ pc[Control] = "ControlerCheckTruck"
                       /\ AvailableTrucks /= {}
                       /\ freetruck' = (CHOOSE t \in AvailableTrucks : TRUE)
                       /\ truckCommand' = [truckCommand EXCEPT ![freetruck'] = [command |-> "request", bin |-> thebin]]
                       /\ pc' = [pc EXCEPT ![Control] = "Fix"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, perm, selectedBin, req, 
                                       tb, scan, permission, thebin >>

Fix == /\ pc[Control] = "Fix"
       /\ thebin' = 0
       /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                       ramExtended, trashInTop, trashCompressed, 
                       trashUncompressed, trashCapacity, trapDestroyed, 
                       userTrash, binCommand, binSensor, scans, permissions, 
                       serverRequests, serverResponses, truckCommand, perm, 
                       selectedBin, req, tb, scan, permission, freetruck >>

controlProcess == ControlStart \/ WaitScan \/ NoPermission
                     \/ ControlAwaitRequest \/ ControlAwaitResponse
                     \/ ConrtolUnlockDoor \/ ControlAwaitUnlockDoor
                     \/ ControlGivePermission \/ ControlLockOuterDoor
                     \/ AwaitLockDoor \/ OpenTrapDoor \/ AwaitOpenTrapDoor
                     \/ CloseTrapDoor \/ AwaitCloseTrapDoor \/ ExtendRam
                     \/ AwaitExtendRam \/ UnExtendRam \/ AwaitUnExtendRam
                     \/ CheckFull \/ ControlerCheckTruck \/ Fix

Next == serverProcess \/ controlProcess
           \/ (\E self \in Bins: binProcess(self))
           \/ (\E self \in Users: userProcess(self))
           \/ (\E self \in Trucks: truckProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Bins : WF_vars(binProcess(self))
        /\ \A self \in Users : WF_vars(userProcess(self))
        /\ WF_vars(serverProcess)
        /\ \A self \in Trucks : WF_vars(truckProcess(self))
        /\ WF_vars(controlProcess)

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Fri Oct 16 11:49:10 CEST 2026 by gjorgji
