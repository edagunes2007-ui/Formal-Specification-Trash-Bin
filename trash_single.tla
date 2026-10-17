---------------------------- MODULE trash_single ----------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bin
  outerDoorOpen = FALSE,
  outerDoorLocked = TRUE,
  trapDoorOpen = FALSE,
  ramExtended = FALSE,
  trashInTop = 0,
  trashCompressed = 0,
  trashUncompressed = 0,
  trashCapacity = MaxCapacity,
  trapDestroyed = FALSE,

  \* Variable for user
  userTrash = 0,

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [command |-> "finished", open |-> FALSE],
  \* Sensor from bin
  binSensor = [sensor |-> "idle"],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = << >>,
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Command for the truck
  truckCommand = [command |-> "emptied", bin |-> 1];
  \* Current permission: 
  permission = [user |-> 0, bin |-> 1, granted |-> FALSE]
   

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity


\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.

\* The outer door can only be locked if it is closed.
OuterDoorLocked == outerDoorLocked => ~outerDoorOpen

\* The vertical ram is only used when the outer door is closed and locked.
RamOuterDoor == ramExtended => (outerDoorLocked /\ ~outerDoorOpen)

\* An unauthorized user cannot open the outer door.
AuthorizedOpenOnly == [](outerDoorOpen => permission.permission = TRUE)

\* Every time the trash bin is full, it is eventually not full anymore.
TrashEmptied == [](CapacityExceeded => <>~CapacityExceeded)

\* The user infinitely often has trash and infinitely often has no trash.
UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)

\* Every time the user has trash, they can deposit their trash.
UserTrashDeposited == [](userTrash > 0 => <>(userTrash = 0))

\* Every time the truck is requested, the bin is eventually emptied.
TruckEmpties == [](truckCommand.command = "request" => <>(truckCommand.command = "emptied"))
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
      await binCommand.command /= "finished";
      if binCommand.command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked;
        outerDoorOpen := binCommand.open;
        if ~outerDoorOpen then
          binSensor := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand.command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen;
        outerDoorLocked := ~(binCommand.open);
      elsif binCommand.command = "change_trap_door" then
        assert outerDoorLocked;
        \* Open/Close trap door
        if ramExtended \/ CapacityExceeded then
            trapDestroyed := TRUE;
        end if;
        trapDoorOpen := binCommand.open;
        if trapDoorOpen then
          \* Trash falls through
          trashUncompressed := trashUncompressed + trashInTop;
          trashInTop := 0;
        end if
      elsif binCommand.command = "change_ram" then
        assert outerDoorLocked;
        \* Extend/Retract ram
        ramExtended := binCommand.open;
        if ramExtended then
          if ~trapDoorOpen then
            trapDestroyed := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed, trashUncompressed);
        end if;
      elsif binCommand.command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked;
        assert ~trapDoorOpen;
        assert ~ramExtended;
        assert trashInTop = 0;
        assert trashUncompressed = 0;
        trashCompressed := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand.command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE]
begin
  UserNextIteration:
    while TRUE do
      if userTrash = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash := amt;
        end with;
      end if;
  UserScanCard:
      write(scans, [user |-> self, bin |-> 1]);
  UserAwaitScanResponse:
      read(permissions, perm);
      assert perm.user = self;
      assert perm.bin = 1;
      if perm.granted then
  UserOpenDoor:
        binCommand := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand.command = "finished";
  UserDepositTrash:
        assert trashInTop = 0;
        trashInTop := userTrash;
        userTrash := 0;
  UserCloseDoor:
        binCommand := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand.command = "finished";
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
\* Remodel it to react to requests and empty the trash bin!
fair process truckProcess \in Trucks
begin
  TruckStart:
  while TRUE do
    await truckCommand.command = "request";
    assert truckCommand.bin = 1;
    truckCommand.command := "arrived";
    
    TruckSendEmpty:
    await binCommand.command = "finished";
    binCommand := [command |-> "empty", open |-> FALSE];
    truckCommand.command := "start_emptying";
    
    TruckStartEmptying:
    await binCommand.command = "finished";
    truckCommand := [command |-> "emptied", bin |-> 1];
  end while;
end process;



\*****************************
\* Process for the controller
\*****************************
fair process controlProcess = Control
variables
  scan = [user |-> 0, bin |-> 0],
begin
  ControlStart:
   while TRUE do
  
     if truckCommand.command # "emptied" then 
        NoPermission:
            read(scans,scan);
            write(permissions, [user |-> scan.user, bin |-> 1, granted |-> FALSE]);
            
     else 
        ControlAwaitRequest:
           read(scans,scan);
           write(serverRequests, [user |-> scan.user]);
           
        ControlAwaitResponse:
           read(serverResponses, permission);
           if permission.permission then
             ConrtolUnlockDoor:
                binCommand := [command |-> "change_outer_lock", open |-> TRUE];
             ControlAwaitUnlockDoor:
                await binCommand.command = "finished";
             ControlGivePermission:
                write(permissions, [user |-> permission.user, bin |-> 1, granted |-> TRUE]);
             ControlLockOuterDoor:
                await ~outerDoorOpen /\ trashInTop > 0 /\ binCommand.command = "finished";
                binCommand := [command |-> "change_outer_lock", open |-> FALSE];
             AwaitLockDoor:
                await binCommand.command = "finished";
             OpenTrapDoor:
                binCommand := [command |-> "change_trap_door", open |-> TRUE];
             AwaitOpenTrapDoor:
                await binCommand.command = "finished";
             CloseTrapDoor:
                binCommand := [command |-> "change_trap_door", open |-> FALSE];
             AwaitCloseTrapDoor:
                await binCommand.command = "finished";
             ExtendRam:
                binCommand := [command |-> "change_ram", open |-> TRUE];
             AwaitExtendRam:
                await binCommand.command = "finished";
             UnExtendRam:
                binCommand := [command |-> "change_ram", open |-> FALSE];
             AwaitUnExtendRam:
                await binCommand.command = "finished";
                
             CheckFull:
                 if Trash >= 4  then 
                   truckCommand.command:= "request" 
                 end if;
                 
           else 
                write(permissions, [user |-> permission.user, bin |-> 1, granted |-> FALSE]);
           end if;
      end if;
    end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "46d9a0e9" /\ chksum(tla) = "fbb6e18b")
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, binCommand, binSensor, scans, permissions, 
          serverRequests, serverResponses, truckCommand, permission, pc

(* define statement *)
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity






TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins


MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded








OuterDoorLocked == outerDoorLocked => ~outerDoorOpen


RamOuterDoor == ramExtended => (outerDoorLocked /\ ~outerDoorOpen)


AuthorizedOpenOnly == [](outerDoorOpen => permission.permission = TRUE)


TrashEmptied == [](CapacityExceeded => <>~CapacityExceeded)


UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)


UserTrashDeposited == [](userTrash > 0 => <>(userTrash = 0))


TruckEmpties == [](truckCommand.command = "request" => <>(truckCommand.command = "emptied"))

VARIABLES perm, req, scan

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, binCommand, binSensor, scans, 
           permissions, serverRequests, serverResponses, truckCommand, 
           permission, pc, perm, req, scan >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = FALSE
        /\ outerDoorLocked = TRUE
        /\ trapDoorOpen = FALSE
        /\ ramExtended = FALSE
        /\ trashInTop = 0
        /\ trashCompressed = 0
        /\ trashUncompressed = 0
        /\ trashCapacity = MaxCapacity
        /\ trapDestroyed = FALSE
        /\ userTrash = 0
        /\ binCommand = [command |-> "finished", open |-> FALSE]
        /\ binSensor = [sensor |-> "idle"]
        /\ scans = << >>
        /\ permissions = << >>
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [command |-> "emptied", bin |-> 1]
        /\ permission = [user |-> 0, bin |-> 1, granted |-> FALSE]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process controlProcess *)
        /\ scan = [user |-> 0, bin |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckStart"
                                        [] self = Control -> "ControlStart"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand.command /= "finished"
                           /\ IF binCommand.command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked, 
                                                "Failure of assertion at line 170, column 9.")
                                      /\ outerDoorOpen' = binCommand.open
                                      /\ IF ~outerDoorOpen'
                                            THEN /\ binSensor' = [sensor |-> "outer_door_closed"]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand.command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen, 
                                                           "Failure of assertion at line 177, column 9.")
                                                 /\ outerDoorLocked' = ~(binCommand.open)
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand.command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked, 
                                                                      "Failure of assertion at line 180, column 9.")
                                                            /\ IF ramExtended \/ CapacityExceeded
                                                                  THEN /\ trapDestroyed' = TRUE
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = binCommand.open
                                                            /\ IF trapDoorOpen'
                                                                  THEN /\ trashUncompressed' = trashUncompressed + trashInTop
                                                                       /\ trashInTop' = 0
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand.command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked, 
                                                                                 "Failure of assertion at line 192, column 9.")
                                                                       /\ ramExtended' = binCommand.open
                                                                       /\ IF ramExtended'
                                                                             THEN /\ IF ~trapDoorOpen
                                                                                        THEN /\ trapDestroyed' = TRUE
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = (trashCompressed + IF (trashUncompressed > 1) THEN trashUncompressed \div 2 ELSE trashUncompressed)
                                                                                  /\ trashUncompressed' = 0
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand.command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked, 
                                                                                            "Failure of assertion at line 204, column 9.")
                                                                                  /\ Assert(~trapDoorOpen, 
                                                                                            "Failure of assertion at line 205, column 9.")
                                                                                  /\ Assert(~ramExtended, 
                                                                                            "Failure of assertion at line 206, column 9.")
                                                                                  /\ Assert(trashInTop = 0, 
                                                                                            "Failure of assertion at line 207, column 9.")
                                                                                  /\ Assert(trashUncompressed = 0, 
                                                                                            "Failure of assertion at line 208, column 9.")
                                                                                  /\ trashCompressed' = 0
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 212, column 9.")
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
                                           truckCommand, permission, perm, req, 
                                           scan >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT !.command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            truckCommand, permission, perm, 
                                            req, scan >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           permission, perm, req, scan >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ scans' = Append(scans, ([user |-> self, bin |-> 1]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, permission, perm, req, 
                                      scan >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 239, column 7.")
                               /\ Assert(perm'[self].bin = 1, 
                                         "Failure of assertion at line 240, column 7.")
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
                                               truckCommand, permission, req, 
                                               scan >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [command |-> "change_outer_door", open |-> TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, permission, perm, req, 
                                      scan >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand.command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           permission, perm, req, scan >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop = 0, 
                                    "Failure of assertion at line 247, column 9.")
                          /\ trashInTop' = userTrash
                          /\ userTrash' = 0
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, scans, 
                                          permissions, serverRequests, 
                                          serverResponses, truckCommand, 
                                          permission, perm, req, scan >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [command |-> "change_outer_door", open |-> FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, permission, perm, req, 
                                       scan >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand.command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, scans, 
                                             permissions, serverRequests, 
                                             serverResponses, truckCommand, 
                                             permission, perm, req, scan >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = amt
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, permission, perm, req, 
                                      scan >>

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
                                       serverResponses, truckCommand, 
                                       permission, perm, req, scan >>

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
                                      permissions, truckCommand, permission, 
                                      perm, scan >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckStart(self) == /\ pc[self] = "TruckStart"
                    /\ truckCommand.command = "request"
                    /\ Assert(truckCommand.bin = 1, 
                              "Failure of assertion at line 287, column 5.")
                    /\ truckCommand' = [truckCommand EXCEPT !.command = "arrived"]
                    /\ pc' = [pc EXCEPT ![self] = "TruckSendEmpty"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    permission, perm, req, scan >>

TruckSendEmpty(self) == /\ pc[self] = "TruckSendEmpty"
                        /\ binCommand.command = "finished"
                        /\ binCommand' = [command |-> "empty", open |-> FALSE]
                        /\ truckCommand' = [truckCommand EXCEPT !.command = "start_emptying"]
                        /\ pc' = [pc EXCEPT ![self] = "TruckStartEmptying"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binSensor, scans, 
                                        permissions, serverRequests, 
                                        serverResponses, permission, perm, req, 
                                        scan >>

TruckStartEmptying(self) == /\ pc[self] = "TruckStartEmptying"
                            /\ binCommand.command = "finished"
                            /\ truckCommand' = [command |-> "emptied", bin |-> 1]
                            /\ pc' = [pc EXCEPT ![self] = "TruckStart"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binCommand, binSensor, scans, 
                                            permissions, serverRequests, 
                                            serverResponses, permission, perm, 
                                            req, scan >>

truckProcess(self) == TruckStart(self) \/ TruckSendEmpty(self)
                         \/ TruckStartEmptying(self)

ControlStart == /\ pc[Control] = "ControlStart"
                /\ IF truckCommand.command # "emptied"
                      THEN /\ pc' = [pc EXCEPT ![Control] = "NoPermission"]
                      ELSE /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitRequest"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, permissions, serverRequests, 
                                serverResponses, truckCommand, permission, 
                                perm, req, scan >>

NoPermission == /\ pc[Control] = "NoPermission"
                /\ scans /= <<>>
                /\ scan' = Head(scans)
                /\ scans' = Tail(scans)
                /\ permissions' = Append(permissions, ([user |-> scan'.user, bin |-> 1, granted |-> FALSE]))
                /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, serverRequests, serverResponses, 
                                truckCommand, permission, perm, req >>

ControlAwaitRequest == /\ pc[Control] = "ControlAwaitRequest"
                       /\ scans /= <<>>
                       /\ scan' = Head(scans)
                       /\ scans' = Tail(scans)
                       /\ serverRequests' = Append(serverRequests, ([user |-> scan'.user]))
                       /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitResponse"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, permissions, 
                                       serverResponses, truckCommand, 
                                       permission, perm, req >>

ControlAwaitResponse == /\ pc[Control] = "ControlAwaitResponse"
                        /\ serverResponses /= <<>>
                        /\ permission' = Head(serverResponses)
                        /\ serverResponses' = Tail(serverResponses)
                        /\ IF permission'.permission
                              THEN /\ pc' = [pc EXCEPT ![Control] = "ConrtolUnlockDoor"]
                                   /\ UNCHANGED permissions
                              ELSE /\ permissions' = Append(permissions, ([user |-> permission'.user, bin |-> 1, granted |-> FALSE]))
                                   /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binCommand, binSensor, 
                                        scans, serverRequests, truckCommand, 
                                        perm, req, scan >>

ConrtolUnlockDoor == /\ pc[Control] = "ConrtolUnlockDoor"
                     /\ binCommand' = [command |-> "change_outer_lock", open |-> TRUE]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitUnlockDoor"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, permission, perm, req, scan >>

ControlAwaitUnlockDoor == /\ pc[Control] = "ControlAwaitUnlockDoor"
                          /\ binCommand.command = "finished"
                          /\ pc' = [pc EXCEPT ![Control] = "ControlGivePermission"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashInTop, trashCompressed, 
                                          trashUncompressed, trashCapacity, 
                                          trapDestroyed, userTrash, binCommand, 
                                          binSensor, scans, permissions, 
                                          serverRequests, serverResponses, 
                                          truckCommand, permission, perm, req, 
                                          scan >>

ControlGivePermission == /\ pc[Control] = "ControlGivePermission"
                         /\ permissions' = Append(permissions, ([user |-> permission.user, bin |-> 1, granted |-> TRUE]))
                         /\ pc' = [pc EXCEPT ![Control] = "ControlLockOuterDoor"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userTrash, binCommand, binSensor, 
                                         scans, serverRequests, 
                                         serverResponses, truckCommand, 
                                         permission, perm, req, scan >>

ControlLockOuterDoor == /\ pc[Control] = "ControlLockOuterDoor"
                        /\ ~outerDoorOpen /\ trashInTop > 0 /\ binCommand.command = "finished"
                        /\ binCommand' = [command |-> "change_outer_lock", open |-> FALSE]
                        /\ pc' = [pc EXCEPT ![Control] = "AwaitLockDoor"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binSensor, scans, 
                                        permissions, serverRequests, 
                                        serverResponses, truckCommand, 
                                        permission, perm, req, scan >>

AwaitLockDoor == /\ pc[Control] = "AwaitLockDoor"
                 /\ binCommand.command = "finished"
                 /\ pc' = [pc EXCEPT ![Control] = "OpenTrapDoor"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binCommand, 
                                 binSensor, scans, permissions, serverRequests, 
                                 serverResponses, truckCommand, permission, 
                                 perm, req, scan >>

OpenTrapDoor == /\ pc[Control] = "OpenTrapDoor"
                /\ binCommand' = [command |-> "change_trap_door", open |-> TRUE]
                /\ pc' = [pc EXCEPT ![Control] = "AwaitOpenTrapDoor"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binSensor, scans, 
                                permissions, serverRequests, serverResponses, 
                                truckCommand, permission, perm, req, scan >>

AwaitOpenTrapDoor == /\ pc[Control] = "AwaitOpenTrapDoor"
                     /\ binCommand.command = "finished"
                     /\ pc' = [pc EXCEPT ![Control] = "CloseTrapDoor"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, permission, perm, req, scan >>

CloseTrapDoor == /\ pc[Control] = "CloseTrapDoor"
                 /\ binCommand' = [command |-> "change_trap_door", open |-> FALSE]
                 /\ pc' = [pc EXCEPT ![Control] = "AwaitCloseTrapDoor"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binSensor, scans, 
                                 permissions, serverRequests, serverResponses, 
                                 truckCommand, permission, perm, req, scan >>

AwaitCloseTrapDoor == /\ pc[Control] = "AwaitCloseTrapDoor"
                      /\ binCommand.command = "finished"
                      /\ pc' = [pc EXCEPT ![Control] = "ExtendRam"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, serverRequests, 
                                      serverResponses, truckCommand, 
                                      permission, perm, req, scan >>

ExtendRam == /\ pc[Control] = "ExtendRam"
             /\ binCommand' = [command |-> "change_ram", open |-> TRUE]
             /\ pc' = [pc EXCEPT ![Control] = "AwaitExtendRam"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binSensor, scans, permissions, 
                             serverRequests, serverResponses, truckCommand, 
                             permission, perm, req, scan >>

AwaitExtendRam == /\ pc[Control] = "AwaitExtendRam"
                  /\ binCommand.command = "finished"
                  /\ pc' = [pc EXCEPT ![Control] = "UnExtendRam"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, userTrash, binCommand, 
                                  binSensor, scans, permissions, 
                                  serverRequests, serverResponses, 
                                  truckCommand, permission, perm, req, scan >>

UnExtendRam == /\ pc[Control] = "UnExtendRam"
               /\ binCommand' = [command |-> "change_ram", open |-> FALSE]
               /\ pc' = [pc EXCEPT ![Control] = "AwaitUnExtendRam"]
               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                               ramExtended, trashInTop, trashCompressed, 
                               trashUncompressed, trashCapacity, trapDestroyed, 
                               userTrash, binSensor, scans, permissions, 
                               serverRequests, serverResponses, truckCommand, 
                               permission, perm, req, scan >>

AwaitUnExtendRam == /\ pc[Control] = "AwaitUnExtendRam"
                    /\ binCommand.command = "finished"
                    /\ pc' = [pc EXCEPT ![Control] = "CheckFull"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, permission, perm, req, scan >>

CheckFull == /\ pc[Control] = "CheckFull"
             /\ IF Trash >= 4
                   THEN /\ truckCommand' = [truckCommand EXCEPT !.command = "request"]
                   ELSE /\ TRUE
                        /\ UNCHANGED truckCommand
             /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binCommand, binSensor, scans, 
                             permissions, serverRequests, serverResponses, 
                             permission, perm, req, scan >>

controlProcess == ControlStart \/ NoPermission \/ ControlAwaitRequest
                     \/ ControlAwaitResponse \/ ConrtolUnlockDoor
                     \/ ControlAwaitUnlockDoor \/ ControlGivePermission
                     \/ ControlLockOuterDoor \/ AwaitLockDoor
                     \/ OpenTrapDoor \/ AwaitOpenTrapDoor \/ CloseTrapDoor
                     \/ AwaitCloseTrapDoor \/ ExtendRam \/ AwaitExtendRam
                     \/ UnExtendRam \/ AwaitUnExtendRam \/ CheckFull

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
\* Last modified Sat Oct 17 12:42:41 CEST 2026 by gjorgji
\* Last modified Fri Oct 09 11:11:08 CEST 2026 by 20254458
