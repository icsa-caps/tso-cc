--------------------------------------------------------------------------------
-- TSO-CC Cache Coherence Protocol
--
-- This model uses the Murphi model checker to show that
-- the TSO-CC cache coherence protocol adheres to TSO.
-- We use TSO-LB a finite state simplified model of TSO, sufficent for this
-- verification (proven stronger than TSO seperately).
-- Our verification condition is that there exists a refinement between 
-- TSO-CC and TSO-LB.
-- The model is parameterised for an unbounded number of processors.
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Constants {{{
--------------------------------------------------------------------------------

const
    -- Number of processors, each of which has its own private L1Cache.
    -- NB: this is the number of concrete processors for the parameterisation.
    -- The number of processors modelled by the parameterisation is unbounded.
    PROCS: 2;
    -- Number of addresses to handle
    ADDRS: 3;
    -- Number of values to handle
    VALS: 2;

    -- Network parameters.
    VC_REQ: 0; --Lowest prio
    VC_RES: 1;
    VC_UNB: 2; --Highest prio
    CHAN_MAX: 2; --Number of highest prio VC
    -- Maximum number of messages on network
    -- NB: this is proportional to the number of processors
    NET_MAX: ((2 * (PROCS + 1)) + 1) * ADDRS; --(PROCS + 1) accounts for AbsCache
    

-- }}}

--------------------------------------------------------------------------------
-- Types {{{
-- We set up Murphi types for each of the components of the model.
--------------------------------------------------------------------------------

type
    Cache: scalarset(PROCS); -- Unordered range of processors
    Address: scalarset(ADDRS);         -- Unordered range of memory addresses
    Value: scalarset(VALS);           -- set of values
    Directory: enum { Dir0 };             -- Need enumeration for IsMember calls
    AbsCache: enum { Other0 };
    Node: union { Directory, Cache, AbsCache };
    
    Channel: 0..CHAN_MAX;
    AckCount: 0..PROCS;        --Range of Ack msg counts
    AckSet: multiset [PROCS+2] of Node; --AckROs awaited

    MsgType: enum {
        DataS,
        DataX,
        FwdS,
        FwdX,
        Ack,
        InvRO,
        GetS,
        GetX,
        Data,
        AckC,
        PutE,
        AckRO
    };
    
    MsgState: enum { --State sent in Data messages
        M_E,
        M_S,
        M_SRO
    };

    Message: 
        record
            mtype: MsgType;
            vc: Channel;
            src: Node;
            dst: Node;
            addr: Address;
            val: Value;
            state: MsgState;
            owner: Node;
            ack_cnt: AckCount;
        end;

    CacheState: --Cache state per address
        record
            state: enum {
                C_I,
                C_E,
                C_M,
                C_S,
                C_SRO,
                C_WS,
                C_WSROI,
                C_WX,
                C_WEI,
                C_WMI
            };
            val: Value; --value at addresss
            acnt: boolean; --access count (abstract, either hit or not)
        end;

    DirState: --Directory state per address
        record
            state: enum {
                D_I,
                D_U,
                D_E,
                D_S,
                D_SRO,
                D_WE1,
                D_WE2,
                D_WU1,
                D_WU2,
                D_WEn,
                D_WS
            };
            owners: multiset [PROCS+1] of Node;
            sharers: multiset [PROCS+1] of Node;
            val: Value; --value at address
            need_acks: AckSet; --set of InvRO Acks waited on
            --fromWEn: Boolean; --Track SRO for parameterisation
        end;

    

-- }}}

--------------------------------------------------------------------------------
-- Variables {{{
-- Instantiation of the components
--------------------------------------------------------------------------------

var
    caches: array [Cache] of array [Address] of CacheState;
    dir:    array [Address] of DirState; 
    net:    array [Node] of multiset [NET_MAX+1] of Message; --unordered msg buffer
    --memory model
    lbuffer:    array [Cache] of array [Address] of Value; --local buffers
    gbuffer:    array [Address] of Value; --global buffer

    -- }}}

--------------------------------------------------------------------------------
-- Message functions {{{
-- Murphi functions which relate to the passing of messages
--------------------------------------------------------------------------------

procedure Send(
    mtype: MsgType;
    vc: Channel;
    src: Node;
    dst: Node;
    addr: Address;
    val: Value;
    state: MsgState;
    owner: Node;
    ack_cnt: AckCount);
var
    msg:Message;
begin
    msg.mtype := mtype;
    msg.vc := vc;
    msg.src := src;
    msg.dst := dst;
    msg.addr := addr;
    msg.val := val;
    msg.state := state;
    msg.ack_cnt := ack_cnt;
    Assert (MultiSetCount(i:net[dst], true) < NET_MAX) "Too many messages!";
    MultiSetAdd(msg, net[dst]);
end;

--Send GetS
procedure SendGetS(
    src: Node;
    dst: Node;
    addr: Address);
begin
    if (dst != Other0) then
        Send(GetS,VC_REQ,src,dst,addr,UNDEFINED,UNDEFINED,UNDEFINED,UNDEFINED);
    endif;
end;

--Send GetX
procedure SendGetX(
    src: Node;
    dst: Node;
    addr: Address;
    val: Value);
begin
    if (dst != Other0) then
        Send(GetX,VC_REQ,src,dst,addr,val,UNDEFINED,UNDEFINED,UNDEFINED);
    endif;
end;

--Send Data
procedure SendData(
    src: Node;
    dst: Node;
    addr: Address;
    val: Value);
begin
    if (dst != Other0) then
        Send(Data,VC_RES,src,dst,addr,val,UNDEFINED,UNDEFINED,UNDEFINED);
    endif;
end;

--Send AckC
procedure SendAckC(
    src: Node;
    dst: Node;
    addr: Address;
    ack_cnt: AckCount);
begin
    if (dst != Other0) then
        Send(AckC,VC_UNB,src,dst,addr,UNDEFINED,UNDEFINED,UNDEFINED,ack_cnt);
    endif;
end;

--Send PutE
procedure SendPutE(
    src: Node;
    dst: Node;
    addr: Address);
begin
    if (dst != Other0) then
        Send(PutE,VC_REQ,src,dst,addr,UNDEFINED,UNDEFINED,UNDEFINED,UNDEFINED);
    endif;
end;

--Send AckRO
procedure SendAckRO(
    src: Node;
    dst: Node;
    addr: Address);
begin
    if (dst != Other0) then
        Send(AckRO,VC_UNB,src,dst,addr,UNDEFINED,UNDEFINED,UNDEFINED,UNDEFINED);
    endif;
end;

--Send DataS
procedure SendDataS(
    src: Node;
    dst: Node;
    addr: Address;
    val: Value;
    state: MsgState;
    owner: Node);
begin
    if (dst != Other0) then
        Send(DataS,VC_RES,src,dst,addr,val,state,owner,UNDEFINED);
    endif;
end;

--Send DataX
procedure SendDataX(
    src: Node;
    dst: Node;
    addr: Address;
    val: Value;
    owner: Node;
    ack_cnt: AckCount);
begin
    if (dst != Other0) then
        Send(DataX,VC_RES,src,dst,addr,val,UNDEFINED,owner,ack_cnt);
    endif;
end;

--Send FwdS
procedure SendFwdS(
    src: Node;
    dst: Node;
    addr: Address);
begin
    if (dst != Other0) then
        Send(FwdS,VC_REQ,src,dst,addr,UNDEFINED,UNDEFINED,UNDEFINED,UNDEFINED);
    endif;
end;

--Send FwdX
procedure SendFwdX(
    src: Node;
    dst: Node;
    addr: Address;
    val: Value);
begin
    if (dst != Other0) then
        Send(FwdX,VC_REQ,src,dst,addr,val,UNDEFINED,UNDEFINED,UNDEFINED);
    endif;
end;

--Send Ack
procedure SendAck(
    src: Node;
    dst: Node;
    addr: Address);
begin
    if (dst != Other0) then
        Send(Ack,VC_UNB,src,dst,addr,UNDEFINED,UNDEFINED,UNDEFINED,UNDEFINED);
    endif;
end;

--Send InvRO
procedure SendInvRO(
    src: Node;
    dst: Node;
    addr: Address);
begin
    if (dst != Other0) then
        Send(InvRO,VC_UNB,src,dst,addr,UNDEFINED,UNDEFINED,UNDEFINED,UNDEFINED);
    endif;
end;

-- Errors
procedure ErrorUnhandledMessage();
begin
    error "Unhandled message type!";
end;

procedure ErrorUnhandledState();
begin
  error "Unhandled state!";
end;


-- }}}

--------------------------------------------------------------------------------
-- Memory consistency operational model {{{
-- This is the Muprhi model of TSO-LB
-- The functions which correspond to the rules of TSO-LB are called from the 
-- rules of TSO-CC (below) to ensure that there is a refinement mapping 
-- between the two models for every observable action (read/write).
--------------------------------------------------------------------------------

procedure TSOStore(c:Cache; a:Address; v:Value);
--Write to store buffer
begin
    lbuffer[c][a] := v;
    gbuffer[a] := v;
end;

procedure TSOStoreAbs(a:Address; v:Value);
--Write to store buffer from an abstract cache
begin
    gbuffer[a] := v;
end;


procedure TSOUpdate(c:Cache);
--At any time we can update the local buffer
-- from the global. In this model we do it on
-- Data send (from Dir or Fwder)
begin
    for a:Address do
        lbuffer[c][a] := gbuffer[a];
    endfor;
end;

function TSOVerify(c:Cache; a:Address; v:Value) : boolean;
--Read from memory
-- and verify that value (v) is a possible read
begin
    if lbuffer[c][a] = v then
        return true;
    else
        TSOUpdate(c);
        return lbuffer[c][a] = v;
    end;
end;

-- }}}

--------------------------------------------------------------------------------
-- Directory functions {{{
-- These correspond to the rules of TSO-CC for the Directory
--------------------------------------------------------------------------------

-- Add to sharers
procedure AddToSharers(n:Node;a:Address);
begin
    if MultiSetCount(i:dir[a].sharers, dir[a].sharers[i] = n) = 0
    then
        MultiSetAdd(n, dir[a].sharers);
    endif;
end;

-- Remove from sharers
procedure RemoveFromSharers(n:Node;a:Address);
begin
    MultiSetRemovePred(i:dir[a].sharers, dir[a].sharers[i] = n);
end;

-- Replace sharers
procedure ReplaceSharers(n:Node;a:Address);
begin
    undefine dir[a].sharers;
    MultisetAdd(n, dir[a].sharers);
end;


-- Add to owners
procedure AddToOwners(n:Node;a:Address);
begin
    if MultiSetCount(i:dir[a].owners, dir[a].owners[i] = n) = 0
    then
        MultiSetAdd(n, dir[a].owners);
    endif;
end;

-- Remove from owners
procedure RemoveFromOwners(n:Node;a:Address);
begin
    MultiSetRemovePred(i:dir[a].owners, dir[a].owners[i] = n);
end;

-- Replace owner
procedure ReplaceOwner(n:Node;a:Address);
begin
    undefine dir[a].owners;
    MultisetAdd(n, dir[a].owners);
end;

-- Is owner?
function IsOwner(n:Node;a:Address) : boolean;
begin
    return (MultiSetCount(i:dir[a].owners, dir[a].owners[i] = n) != 0)
end;

--Get owner
--  Return exclusive owner
function GetOwner(a:Address) : Node;
var
    u:Node;
begin
    if MultiSetCount(i:dir[a].owners, true) = 1 then
        for c:Node do
            if (MultiSetCount(i:dir[a].owners, dir[a].owners[i] = c) != 0) then
                return c
            endif;
        endfor;
    else
        u := UNDEFINED;
        return u;
    endif;
end;

-- Add sharers to owners
procedure AddSharersToOwners(a:Address);
begin
    for c:Node do
        if MultiSetCount(i:dir[a].sharers, dir[a].sharers[i] = c) = 1 then
            AddToOwners(c,a);
        endif;
    endfor;
end;

-- Add to NeedAcks
procedure AddToNeedAcks(n:Node;a:Address);
begin
    if MultiSetCount(i:dir[a].need_acks, dir[a].need_acks[i] = n) = 0
    then
        MultiSetAdd(n, dir[a].need_acks);
    endif;
end;

-- Remove from NeedAcks
procedure RemoveFromNeedAcks(n:Node;a:Address);
begin
    MultiSetRemovePred(i:dir[a].need_acks, dir[a].need_acks[i] = n);
end;

--IsEmpty NeedAcks?
function IsEmptyNeedAcks(a:Address) : boolean;
begin
    return (MultiSetCount(i:dir[a].need_acks, true) = 0)
end;

-- Broadcast InvRO (and set need_acks)
procedure BCastInvRO(src:Node;a:Address);
begin
    for c:Node do
        if ((MultiSetCount(i:dir[a].owners, dir[a].owners[i] = c) != 0)
            & (c != src))
        then
            AddToNeedAcks(c,a);
            SendInvRO(Dir0, c, a);
        endif;
    endfor;
end;

--                                    --
-- Receive a message at the Directory --
--                                    --
function DirectoryReceive(msg:Message) : boolean;
begin
    alias blk:dir[msg.addr] do
        switch blk.state
            case D_I:
                switch msg.mtype
                    case GetS:
                        SendDataS(Dir0, msg.src, msg.addr, blk.val, M_E, UNDEFINED);
                        ReplaceOwner(msg.src,msg.addr);
                        blk.state := D_WE1;
                        
                    case GetX:
                        SendDataX(Dir0, msg.src, msg.addr, msg.val, UNDEFINED, 0);
                        ReplaceOwner(msg.src,msg.addr);
                        blk.state := D_WE1;
                        --TSOStore
                        TSOStore(msg.src, msg.addr, msg.val);
                        
                    else ErrorUnhandledMessage();
                endswitch;

            case D_U:
                switch msg.mtype
                    case GetS:
                        SendDataS(Dir0, msg.src, msg.addr, blk.val, 
                                    M_E, GetOwner(msg.addr));
                        ReplaceOwner(msg.src,msg.addr);
                        blk.state := D_WE1;
                        

                    case GetX:
                        SendDataX(Dir0, msg.src, msg.addr, 
                                    blk.val, GetOwner(msg.addr), 0);
                        ReplaceOwner(msg.src,msg.addr);
                        blk.state := D_WE1;
                        --TSOStore
                        TSOStore(msg.src, msg.addr, msg.val);
                                
                    else ErrorUnhandledMessage();
                endswitch;

            case D_E:
                switch msg.mtype
                    case GetS:
                        SendFwdS(msg.src, GetOwner(msg.addr), msg.addr); 
                        ReplaceSharers(msg.src,msg.addr);
                        blk.state := D_WS;
        
                    case GetX:
                        SendFwdX(msg.src, GetOwner(msg.addr), msg.addr, msg.val);
                        ReplaceOwner(msg.src,msg.addr);
                        blk.state := D_WE2;
                        --TSOStore
                        TSOStore(msg.src, msg.addr, msg.val);

                    case Data:
                        --COPY DATA
                        blk.val := msg.val;
                        SendAck(Dir0, msg.src, msg.addr);
                        blk.state := D_U;
                        undefine blk.sharers; --OPT1

                    case PutE:
                        SendAck(Dir0, msg.src, msg.addr);
                        blk.state := D_U;
                        undefine blk.sharers; --OPT1

                    else ErrorUnhandledMessage();
                endswitch;

            case D_S:
                switch msg.mtype
                    case GetS:
                        SendDataS(Dir0, msg.src, msg.addr, 
                                    blk.val, M_S, GetOwner(msg.addr));
                                            
                    case GetX:
                        SendDataX(Dir0, msg.src, msg.addr, msg.val, GetOwner(msg.addr), 0);
                        ReplaceOwner(msg.src,msg.addr);
                        blk.state := D_WE1;
                        --TSOStore
                        TSOStore(msg.src, msg.addr, msg.val);
                        
                    else ErrorUnhandledMessage();
                endswitch;

            case D_SRO:
                switch msg.mtype
                    case GetS:
                        SendDataS(Dir0, msg.src, msg.addr, blk.val, M_SRO, UNDEFINED);
                        AddToOwners(msg.src,msg.addr);
                        
                    case GetX:
                        BCastInvRO(msg.src,msg.addr);
                        ReplaceOwner(msg.src,msg.addr);
                        blk.state := D_WEn;
                        --TSOStore
                        TSOStore(msg.src, msg.addr, msg.val);
            
                    else ErrorUnhandledMessage();
                endswitch;

            case D_WE1:
                switch msg.mtype
                    case GetS:
                        --STALL
                        return false;

                    case GetX:
                        --STALL
                        return false;
        
                    case Data:
                        if IsOwner(msg.src,msg.addr) then
                            --COPY DATA
                            blk.val := msg.val;
                            SendAck(Dir0, msg.src, msg.addr);
                            blk.state := D_WU1;
                        else
                            blk.state := D_E;
                        endif;

                    case AckC:
                        blk.state := D_E;
                        --undefine blk.fromWEn; 

                    case PutE:
                        if IsOwner(msg.src,msg.addr) then
                            SendAck(Dir0, msg.src, msg.addr);
                            blk.state := D_WU1;
                        else
                            blk.state := D_E;
                        endif;
            
                    else ErrorUnhandledMessage();
                endswitch;

            case D_WE2:
                switch msg.mtype
                    case GetS:
                        --STALL
                        return false;

                    case GetX:
                        --STALL
                        return false;
                    
                    case Data:
                        if IsOwner(msg.src,msg.addr) then
                            --COPY DATA
                            blk.val := msg.val;
                            SendAck(Dir0, msg.src, msg.addr);
                            blk.state := D_WU2;
                        else
                            blk.state := D_WE1;
                        endif;

                    case AckC:
                        if msg.ack_cnt = 1 then
                            blk.state := D_E;
                        else
                            blk.state := D_WE1;
                        endif;

                    case PutE:
                        if IsOwner(msg.src,msg.addr) then
                            SendAck(Dir0, msg.src, msg.addr);
                            blk.state := D_WU2;
                        else
                            blk.state := D_WE1;
                        endif;
            
                    else ErrorUnhandledMessage();
                endswitch;

            case D_WU1:
                switch msg.mtype
                    case GetS:
                        --STALL
                        return false;

                    case GetX:
                        --STALL
                        return false;
                    
                    case Data:
                        blk.state := D_U;
                        undefine blk.sharers; --OPT1

                    case AckC:
                        blk.state := D_U;
                        undefine blk.sharers; --OPT1

                    case PutE:
                        blk.state := D_U;
                        undefine blk.sharers; --OPT1
            
                    else ErrorUnhandledMessage();
                endswitch;
                --undefine blk.fromWEn;

            case D_WU2:
                switch msg.mtype
                    case GetS:
                        --STALL
                        return false;

                    case GetX:
                        --STALL
                        return false;
                    
                    case Data:
                        blk.state := D_WU1;

                    case AckC:
                        if msg.ack_cnt = 1 then
                            blk.state := D_U;
                            undefine blk.sharers; --OPT1
                        else
                            blk.state := D_WU1;
                        endif;

                    case PutE:
                        blk.state := D_WU1;
            
                    else ErrorUnhandledMessage();
                endswitch;

            case D_WEn:
                switch msg.mtype
                    case GetS:
                        --STALL
                        return false;

                    case GetX:
                        --STALL
                        return false;
                    
                    case AckRO:
                        RemoveFromNeedAcks(msg.src,msg.addr);
                        if IsEmptyNeedAcks(msg.addr) then
                            SendDataX(Dir0, GetOwner(msg.addr), msg.addr, 
                                        blk.val, UNDEFINED, 0);
                            blk.state := D_WE1;
                            
                        endif;
            
                    else ErrorUnhandledMessage();
                endswitch;

            case D_WS:
                switch msg.mtype
                    case GetS:
                        --STALL
                        return false;

                    case GetX:
                        --STALL
                        return false;
                    
                    case Data:
                        --COPY DATA
                        blk.val := msg.val;
                        blk.state := D_S;

                    case AckC:
                        AddSharersToOwners(msg.addr);
                        AddToOwners(msg.src,msg.addr);
                        blk.state := D_SRO;

                    case PutE:
                        AddSharersToOwners(msg.addr);
                        blk.state := D_SRO;
            
                    else ErrorUnhandledMessage();
                endswitch;
            
            else ErrorUnhandledState();
        endswitch;

        --Message Processed:
        return true;
    endalias;
end;

-- }}}

--------------------------------------------------------------------------------
-- L1Cache functions {{{
-- These correspond to the rules of TSO-CC for the L1 caches
--------------------------------------------------------------------------------

-- Self-invalidate all lines at a cache, except the given:
procedure InvalidateAllOtherLines(c:Cache;a1:Address);
begin
    for a:Address do
        if (a != a1) & (caches[c][a].state = C_S) then
            caches[c][a].state := C_I;
        endif;
    endfor;
end;

--                                --
-- Receive a message at the Cache --
--                                --
function CacheReceive(msg:Message; c:Cache) : boolean;
begin
    alias blk:caches[c][msg.addr] do
        switch blk.state
            case C_I:
                switch msg.mtype
                    case InvRO:
                        SendAckRO(c, Dir0, msg.addr);
                endswitch;

            case C_E:
                switch msg.mtype
                    case InvRO:
                        SendAckRO(c, Dir0, msg.addr);
                    
                    case FwdS:
                        SendDataS(c, msg.src, msg.addr, blk.val, M_SRO, c);
                        SendAckC(c, Dir0, msg.addr, 0);
                        blk.state := C_SRO;
                        
                    case FwdX:
                        SendDataX(c, msg.src, msg.addr, msg.val, c, 1);
                        blk.state := C_S;
                        
                endswitch;

            case C_M:
                switch msg.mtype
                    case InvRO:
                        SendAckRO(c, Dir0, msg.addr);
                    
                    case FwdS:
                        SendDataS(c, msg.src, msg.addr, blk.val, M_S, c);
                        SendData(c, Dir0, msg.addr, blk.val);
                        blk.state := C_S;
                        
                    case FwdX:
                        SendDataX(c, msg.src, msg.addr, msg.val, c, 1);
                        blk.state := C_S;
                        
                endswitch;

            case C_S:
                switch msg.mtype
                    case InvRO:
                        SendAckRO(c, Dir0, msg.addr);
                endswitch;

            case C_SRO:
                switch msg.mtype
                    case InvRO:
                        SendAckRO(c, Dir0, msg.addr);
                        blk.state := C_I;
                endswitch;

            case C_WS:
                switch msg.mtype
                    case InvRO:
                        SendAckRO(c, Dir0, msg.addr);
                        blk.state := C_WSROI;

                    case DataS:
                        --COPY DATA
                        --HIT
                        blk.val := msg.val;
                        --TSOStore 
                        TSOStore(c,msg.addr,msg.val);
                        switch msg.state
                            case M_S:
                                blk.state := C_S;
                            case M_SRO:
                                blk.state := C_SRO;
                            case M_E:
                                SendAckC(c, Dir0, msg.addr, 0);
                                blk.state := C_E;
                        endswitch;
                        InvalidateAllOtherLines(c,msg.addr);
                        --TSOVerify
                        Assert(TSOVerify(c,msg.addr,msg.val));
                endswitch;

            case C_WSROI:
                switch msg.mtype
                    case InvRO:
                        SendAckRO(c, Dir0, msg.addr);

                    case DataS:
                        --COPY DATA
                        --HIT
                        blk.val := msg.val;
                        --TSOStore
                        TSOStore(c,msg.addr,msg.val);
                        switch msg.state
                            case M_S:
                                blk.state := C_S;
                            case M_SRO:
                                blk.state := C_I;
                            case M_E:
                                SendAckC(c, Dir0, msg.addr, 0);
                                blk.state := C_E;
                        endswitch;
                        InvalidateAllOtherLines(c,msg.addr);
                        --TSOVerify
                        Assert(TSOVerify(c,msg.addr,msg.val));
                endswitch;

            case C_WX:
                switch msg.mtype
                    case InvRO:
                        SendAckRO(c, Dir0, msg.addr);
                    
                    case DataX:
                        --HIT
                        blk.val := msg.val;
                        --TSOStore 
                        TSOStore(c,msg.addr,msg.val);
                        SendAckC(c, Dir0, msg.addr, msg.ack_cnt);
                        blk.state := C_M;
                        InvalidateAllOtherLines(c,msg.addr);
                endswitch;

            case C_WEI:
                switch msg.mtype
                    case InvRO:
                        SendAckRO(c, Dir0, msg.addr);
                    
                    case FwdS:
                        SendDataS(c, msg.src, msg.addr, blk.val, M_SRO, c);
                        blk.state := C_I;
                        
                    case FwdX:
                        SendDataX(c, msg.src, msg.addr, msg.val, c, 0);
                        blk.state := C_I;
                       
                    case Ack:
                        blk.state := C_I;
                endswitch;

            case C_WMI:
                switch msg.mtype
                    case InvRO:
                        SendAckRO(c, Dir0, msg.addr);
                    
                    case FwdS:
                        SendDataS(c, msg.src, msg.addr, blk.val, M_S, c);
                        blk.state := C_I;
                        
                    case FwdX:
                        SendDataX(c, msg.src, msg.addr, msg.val, c, 0);
                        blk.state := C_I;
                        
                    case Ack:
                        blk.state := C_I;
                endswitch;

        endswitch;
        --Message Processed:
        return true;
    endalias;
end;


-- }}}
  
--------------------------------------------------------------------------------
-- Rules {{{
-- The top level Murphi rules
-- These correspond ot the L1 actions (read/write/evict) of TSO-CC
--------------------------------------------------------------------------------

-- Test if all cache lines are stable
-- (to enforce an in-order pipeline)
function AllStable() : boolean;
begin
    for c:Cache do
        for a:Address do
            alias line:caches[c][a].state do
                if !(line = C_I | line = C_S 
                    | line = C_E | line = C_M | line = C_SRO) then
                    return false;
                endif;
            endalias;
        endfor;
    endfor;
    return true;
end;

-- Processor actions on L1 Caches:
ruleset c:Cache do
    ruleset a:Address do
        alias blk:caches[c][a] do
            --State I--------------------
            --Read
            rule "I.Read"
                (blk.state = C_I) & AllStable()
            ==>
                SendGetS(c, Dir0, a);
                blk.state := C_WS;
            endrule;
            --Write
            ruleset v:Value do
                rule "I.Write"
                    (blk.state = C_I) & AllStable()
                ==>
                    SendGetX(c, Dir0, a, v);
                    blk.state := C_WX;
                    blk.val := v; 
                endrule;
            endruleset;
            --State E--------------------
            --Write
            ruleset v:Value do
                rule "E.Write"
                    (blk.state = C_E) & AllStable()
                ==>
                    blk.val := v;
                    blk.state := C_M;
                    --TSOStore
                    TSOStore(c,a,v);
                endrule;
            endruleset;
            --Evict
            rule "E.Evict"
                (blk.state = C_E) & AllStable()
            ==>
                SendPutE(c, Dir0, a);
                blk.state := C_WEI;
            endrule;
            --State M--------------------
            --Write
            ruleset v:Value do
                rule "M.Write"
                    (blk.state = C_M) & AllStable()
                ==>
                    blk.val := v;
                    --TSOStore
                    TSOStore(c,a,v);
                endrule;
            endruleset;
            --Evict
            rule "M.Evict"
                (blk.state = C_M) & AllStable()
            ==> 
                SendData(c, Dir0, a, blk.val);
                blk.state := C_WMI;
            endrule;
            --State S--------------------
            --Read (ACNT limit hit)
            rule "S.Read.ACNT=MAX"
                (blk.state = C_S) & AllStable()
            ==>
                SendGetS(c, Dir0, a);
                blk.state := C_WS;
            endrule;
            --Read (ACNT limit not hit)
            rule "S.Read.ACNT<MAX"
                (blk.state = C_S) & AllStable()
            ==>
                --TSOVerify
                Assert(TSOVerify(c,a,blk.val));
            endrule;
            --Write
            ruleset v:Value do
                rule "S.Write"
                    (blk.state = C_S) & AllStable()
                ==> 
                    SendGetX(c, Dir0, a, v);
                    blk.state := C_WX;
                    blk.val := v; 
                endrule;
            endruleset;
            --Evict
            rule "S.Evict"
                (blk.state = C_S) & AllStable()
            ==>
                blk.state := C_I;
            endrule;
            --State SRO------------------
            --Write
            ruleset v:Value do
                rule "SRO.Write"
                    (blk.state = C_SRO) & AllStable()
                ==>
                    SendGetX(c, Dir0, a, v);
                    blk.state := C_WX;
                    blk.val := v; 
                endrule;
            endruleset;
            --Evict
            rule "SRO.Evict"
                (blk.state = C_SRO) & AllStable()
            ==>
                blk.state := C_I;
            endrule;
        endalias;
    endruleset;
endruleset;


--Receive rules:
ruleset n:Node do
    choose msg_id:net[n] do
        alias q:net[n] do
        alias msg:q[msg_id] do
        
        rule "Receive"
            (msg.vc = VC_UNB) --In prio order
                | (msg.vc = VC_RES & MultiSetCount(m:q, q[m].vc = VC_UNB) = 0)
                | (msg.vc = VC_REQ & MultiSetCount(m:q, q[m].vc = VC_UNB) = 0
                                   & MultiSetCount(m:q, q[m].vc = VC_RES) = 0)
        ==>
            if IsMember(n, Directory) then
                if DirectoryReceive(msg) then
                    MultiSetRemove(msg_id, q);
                endif;
            else
                if CacheReceive(msg, n) then
                    MultiSetRemove(msg_id, q);
                endif;
            endif;
        endrule;
        endalias;
        endalias;
    endchoose;
endruleset;


------------------
-- Parameterisation: 
-- These are the messages generated from abstract caches
-- The restrictions on each are added as part of the refinement loop
-- of the parameterisation process and correspond to the non-interference lemmas below.
------------------

-- received at directory

ruleset a:Address do
ruleset v:Value do
ruleset coin:Boolean do

    rule "Dir Recv GetS Abs"
        dir[a].state = D_I
        | dir[a].state = D_U
        | dir[a].state = D_E
        | dir[a].state = D_S
        | dir[a].state = D_SRO
    ==>
        switch dir[a].state
            case D_I:
                ReplaceOwner(Other0,a);
                dir[a].state := D_WE1;
                
            case D_U:
                ReplaceOwner(Other0,a);
                dir[a].state := D_WE1;
                
            case D_E:
                SendFwdS(Other0, GetOwner(a), a);
                ReplaceSharers(Other0,a);
                dir[a].state := D_WS;
                
            case D_SRO:
                AddToOwners(Other0,a);
                
        endswitch;
    endrule;

    rule "Dir Recv GetX Abs"
        dir[a].state = D_I
        | dir[a].state = D_U
        | dir[a].state = D_E
        | dir[a].state = D_S
        | dir[a].state = D_SRO
    ==>
        switch dir[a].state
            case D_I:
                ReplaceOwner(Other0,a);
                dir[a].state := D_WE1;
                
            case D_U:
                ReplaceOwner(Other0,a);
                dir[a].state := D_WE1;
                
            case D_E:
                SendFwdX(Other0, GetOwner(a), a, v);
                ReplaceOwner(Other0,a);
                dir[a].state := D_WE2;
                --TSOStore
                TSOStoreAbs(a,v);
            case D_S:
                ReplaceOwner(Other0,a);
                dir[a].state := D_WE1;
                --TSOStore
                TSOStoreAbs(a,v);
                
            case D_SRO:
                BCastInvRO(Other0,a);
                ReplaceOwner(Other0,a);
                dir[a].state := D_WEn;
                --TSOStore
                TSOStoreAbs(a,v);
        endswitch;
    endrule;
    
    rule "Dir Recv Data Abs"
        (dir[a].state = D_E
        | dir[a].state = D_WE1
        | dir[a].state = D_WE2
        | dir[a].state = D_WU1
        | dir[a].state = D_WU2
        | dir[a].state = D_WS)
        --(Lemma 5)
        & (GetOwner(a) = Other0 | ((MultisetCount(i:net[Dir0], net[Dir0][i].mtype=AckC) = 0 & 
                                    caches[GetOwner(a)][a].state != C_WX
                                    & caches[GetOwner(a)][a].state != C_WS) 
                                    | dir[a].state != D_WE1))
        --(Lemma 8)
        -- No Data in D_E/WS except from owner
        & ((dir[a].state = D_E | dir[a].state =D_WS) -> GetOwner(a) = Other0)
        --(Lemma 12) 
        -- No Data if FwdX in flight:
        & (forall n:Node do (MultiSetCount(i:net[n], net[n][i].mtype=FwdX) = 0) endforall)
        --(Lemma 13)
        -- No Data from abstract non-owner(coin:false) if Put or Data from concrete node in flight
        & (forall n:Node do (forall c:Cache do 
                                (MultiSetCount(i:net[n], ((net[n][i].mtype=PutE | net[n][i].mtype=Data)
                                                            & net[n][i].src=c)) = 0) 
            endforall) endforall)
        --(Lemma 14)
        -- No Data if fromWEn is set
        --& isUndefined(dir[a].fromWEn)
        --(Lemma 15)
        -- No Data when DataS/X from Dir is in flight
        & (forall n:Node do 
                (MultiSetCount(i:net[n], (net[n][i].mtype=DataX | net[n][i].mtype=DataS)
                                            & net[n][i].src=Dir0) = 0) 
            endforall)
    ==>
        switch dir[a].state
            case D_E:
                --COPY DATA
                dir[a].val := v;
                --TSOStore 
                TSOStoreAbs(a,v);
                dir[a].state := D_U;
                undefine dir[a].sharers; --OPT1
            case D_WE1:
                -- here if an abstract node is the owner we toss a coin
                -- to decide if the absNode we are receiveing from
                -- will be the owner or a different absNode.
                if IsOwner(Other0,a) & coin then
                    --COPY DATA
                    dir[a].val := v;
                    --TSOStore 
                    TSOStoreAbs(a,v);
                    dir[a].state := D_WU1;
                else
                    dir[a].state := D_E;
                endif;
            case D_WE2:
                if IsOwner(Other0,a) & coin then
                    --COPY DATA
                    dir[a].val := v;
                    --TSOStore 
                    TSOStoreAbs(a,v);
                    dir[a].state := D_WU2;
                else
                    dir[a].state := D_WE1;
                endif;

            case D_WU1:
                dir[a].state := D_U;
                undefine dir[a].sharers; --OPT1

            case D_WU2:
                dir[a].state := D_WU1;

            case D_WS:
                --COPY DATA
                dir[a].val := v;
                --TSOStore 
                TSOStoreAbs(a,v);
                dir[a].state := D_S;
        endswitch;
    endrule;

    rule "Dir Recv AckC Abs"
            (dir[a].state = D_WE1
            | dir[a].state = D_WE2
            | dir[a].state = D_WU1
            | dir[a].state = D_WU2
            | dir[a].state = D_WS)
            --(Lemma 4)
            -- No AckC unless owner is Other0
            --      OR ((No concrete AckC AND owner.state!=WX/WS) OR dir.state!=WE1)
            & (GetOwner(a) = Other0 | ((MultisetCount(i:net[Dir0], net[Dir0][i].mtype=AckC) = 0 & 
                                        caches[GetOwner(a)][a].state != C_WX
                                        & caches[GetOwner(a)][a].state != C_WS) 
                                        | dir[a].state != D_WE1))
            --(Lemma 10)
            --No AckC if AckC(1) already in flight
            & (MultisetCount(i:net[Dir0], net[Dir0][i].mtype=AckC & net[Dir0][i].ack_cnt=1) = 0)
            --(Lemma 11)
            --No AckC(1) if not owner
            & (coin=true -> GetOwner(a)=Other0)
            --(Lemma 16)
            -- No AckC in D_WS except from owner
            & (dir[a].state = D_WS -> GetOwner(a) = Other0)
            --(Lemma 17) 
            -- No AckC if FwdX in flight:
            & (forall n:Node do (MultiSetCount(i:net[n], net[n][i].mtype=FwdX) = 0) endforall)
            --(Lemma 18)
            -- No AckC(1) (coin:true) if Data in flight
            & (forall n:Node do ((MultiSetCount(i:net[n], net[n][i].mtype=Data) > 0) -> !coin) endforall)
            --(Lemma 19)
            -- No AckC(1) (coin:true) if PutE in flight
            & (forall n:Node do ((MultiSetCount(i:net[n], net[n][i].mtype=PutE) > 0) -> !coin) endforall)
            --(Lemma 20)
            -- No AckC if Data in flight and D_WE1
            & (forall n:Node do ((MultiSetCount(i:net[n], net[n][i].mtype=Data) > 0) -> dir[a].state!=D_WE1) endforall)
            --(Lemma 21)
            -- No AckC if PutE in flight and D_WE1
            & (forall n:Node do ((MultiSetCount(i:net[n], net[n][i].mtype=PutE) > 0) -> dir[a].state!=D_WE1) endforall)
            --(Lemma 22)
            -- No AckC when DataS/X from Dir is in flight
            & (forall n:Node do 
                    (MultiSetCount(i:net[n], (net[n][i].mtype=DataX | net[n][i].mtype=DataS)
                                                & net[n][i].src=Dir0) = 0) 
                endforall)
        ==>
            switch dir[a].state
                case D_WE1:
                    dir[a].state := D_E;
                    --undefine dir[a].fromWEn;
                    
                case D_WE2:
                    -- here we toss a coin to decide if the 
                    -- ack_cnt is 1 or not.
                    if coin then
                        dir[a].state := D_E;
                    else
                        dir[a].state := D_WE1;
                    endif;

                case D_WU1:
                    dir[a].state := D_U;
                    undefine dir[a].sharers; --OPT1

                case D_WU2:
                    if coin then
                        dir[a].state := D_U;
                        undefine dir[a].sharers; --OPT1
                    else
                        dir[a].state := D_WU1;
                    endif;

                case D_WS:
                    AddSharersToOwners(a);
                    AddToOwners(Other0,a);
                    dir[a].state := D_SRO;
            endswitch;
    endrule;

    rule "Dir Recv PutE Abs"
            (dir[a].state = D_E
            | dir[a].state = D_WE1
            | dir[a].state = D_WE2
            | dir[a].state = D_WU1
            | dir[a].state = D_WU2
            | dir[a].state = D_WS)
            -- (Lemma 6)
            & (GetOwner(a) = Other0 | ((MultisetCount(i:net[Dir0], net[Dir0][i].mtype=AckC) = 0 & 
                                        caches[GetOwner(a)][a].state != C_WX
                                        & caches[GetOwner(a)][a].state != C_WS) 
                                        | dir[a].state != D_WE1))
            --(Lemma 23)
            -- No PutE in D_E/WS except from owner
            & ((dir[a].state = D_E | dir[a].state = D_WS) -> GetOwner(a) = Other0)
            --(Lemma 24) 
            -- No Put if FwdX in flight:
            & (forall n:Node do (MultiSetCount(i:net[n], net[n][i].mtype=FwdX) = 0) endforall)
            --(Lemma 25)
            -- No PutE from abstract non-owner(coin:false) if Put or Data from concrete node in flight
            & (forall n:Node do (forall c:Cache do 
                                    (MultiSetCount(i:net[n], ((net[n][i].mtype=PutE | net[n][i].mtype=Data)
                                                                & net[n][i].src=c)) = 0) 
                endforall) endforall)
            --(Lemma 26)
            -- No PutE if fromWEn is set
            --& isUndefined(dir[a].fromWEn)
            --(Lemma 27)
            -- No PutE when DataS/X from Dir is in flight
            & (forall n:Node do 
                    (MultiSetCount(i:net[n], (net[n][i].mtype=DataX | net[n][i].mtype=DataS)
                                                & net[n][i].src=Dir0) = 0) 
                endforall)
        ==>
            switch dir[a].state
                case D_E:
                    dir[a].state := D_U;
                    undefine dir[a].sharers; --OPT1
                case D_WE1:
                    -- here if an abstract node is the owner we toss a coin
                    -- to decide if the absNode we are receiveing from
                    -- will be the owner or a different absNode.
                    if IsOwner(Other0,a) & coin then
                        dir[a].state := D_WU1;
                    else
                        dir[a].state := D_E;
                    endif;
                case D_WE2:
                    if IsOwner(Other0,a) & coin then
                        dir[a].state := D_WU2;
                    else
                        dir[a].state := D_WE1;
                    endif;

                case D_WU1:
                    dir[a].state := D_U;
                    undefine dir[a].sharers; --OPT1

                case D_WU2:
                    dir[a].state := D_WU1;

                case D_WS:
                    AddSharersToOwners(a);
                    dir[a].state := D_SRO;
            endswitch;
    endrule;

    rule "Dir Recv AckRO Abs"
            dir[a].state = D_WEn
        ==>
            -- toss a coin to see if this is the Ack we're waiting for
            if coin then
                RemoveFromNeedAcks(Other0,a);
                if IsEmptyNeedAcks(a) then
                    if GetOwner(a) != Other0 then
                        SendDataX(Dir0, GetOwner(a), a, dir[a].val, UNDEFINED, 0);
                    endif;
                    dir[a].state := D_WE1;
                    
                endif;
            endif;
    endrule;

endruleset; 
endruleset;
endruleset;

-- received at concrete cache

ruleset c:Cache do
ruleset a:Address do
alias blk:caches[c][a] do
    
    ruleset v:Value do
        ruleset mstate:MsgState do
            rule "Cache Recv DataS Abs"
                (blk.state = C_WS
                 | blk.state = C_WSROI)
                -- caches cannot send M_E
                & mstate != M_E
                -- (Lemma 3) 
                -- DataS only comes from Abs when it's received a FwdS
                -- so no GetS in flight from c, no FwdS from c, and no DataS to c
                & (forall n:Node do 
                    (MultiSetCount(i:net[n], net[n][i].mtype=GetS & net[n][i].src=c) = 0) 
                    endforall)
                & (forall n:Node do 
                    (MultiSetCount(i:net[n], net[n][i].mtype=FwdS & net[n][i].src=c) = 0) 
                    endforall)
                & (forall n:Node do 
                    (MultiSetCount(i:net[n], net[n][i].mtype=DataS & net[n][i].dst=c) = 0) 
                    endforall)
                --(Lemma 9)
                -- No DataS to c when in D_WS, unless c is owner
                & (dir[a].state=D_WS -> IsOwner(c,a))
            ==>
                switch blk.state
                    case C_WS:
                        --COPY DATA
                        --HIT
                        blk.val := v;
                        --TSOStore 
                        TSOStore(c,a,v);
                        switch mstate
                            case M_S:
                                blk.state := C_S;
                            case M_SRO:
                                blk.state := C_SRO;
                        endswitch;
                        InvalidateAllOtherLines(c,a);
                        
                    case C_WSROI:
                        --COPY DATA
                        --HIT
                        blk.val := v;
                        --TSOStore 
                        TSOStore(c,a,v);
                        switch mstate
                            case M_S:
                                blk.state := C_S;
                            case M_SRO:
                                blk.state := C_I;
                        endswitch;
                        InvalidateAllOtherLines(c,a);
                        
                endswitch;
            endrule;
        endruleset;

        ruleset coin:Boolean do
            rule "Cache Recv DataX Abs"
                blk.state = C_WX
                --(Lemma 1)
                -- DataX only comes from Abs when it's received a FwdX
                -- so receiver must be owner:
                & IsOwner(c,a)
                --(Lemma 2)
                -- No DataX can be sent when another is in flight:
                & MultisetCount(i:net[c], net[c][i].mtype=DataX) = 0
                --(Lemma 7)
                & !(dir[a].state=D_SRO) & !(dir[a].state=D_WEn)
                --(Lemma 28)
                --No DataX in D_S/WS
                & !(dir[a].state=D_S) & !(dir[a].state=D_WS)
                --(Lemma 29)
                --No DataX in D_U
                & !(dir[a].state=D_U)
                --(Lemma 30)
                --No DataX if FwdX in flight with src=c
                & (forall n:Node do (MultiSetCount(i:net[n], net[n][i].mtype=FwdX
                                                            & net[n][i].src=c) = 0) endforall)
                --(Lemma 31)
                --No DataX in D_WU1/2
                & !(dir[a].state=D_WU1) & !(dir[a].state=D_WU2)
            ==>
                if coin then
                    SendAckC(c, Dir0, a, 1); 
                else
                    SendAckC(c, Dir0, a, 0);
                endif;
                blk.state := C_M;
                InvalidateAllOtherLines(c,a);
            endrule;
        endruleset;
    endruleset;

endalias;
endruleset;
endruleset;

------------------


-- }}}

--------------------------------------------------------------------------------
-- Startstate {{{
--------------------------------------------------------------------------------


ruleset v:Value do
    startstate
        for a:Address do
            --Directory
            dir[a].state := D_I;
            undefine dir[a].sharers;
            undefine dir[a].owners;
            dir[a].val := v;
            
            --memory model
            gbuffer[a] := v;
            
            --Caches
            for c:Cache do
                caches[c][a].state := C_I;
                caches[c][a].val := v;
                
                --memory model
                lbuffer[c][a] := v;
            endfor;
        endfor;
    endstartstate;
endruleset;


-- }}}

--------------------------------------------------------------------------------
-- Invariants {{{
--------------------------------------------------------------------------------

--Model optimisations

invariant "[Model opt.] I or U implies no sharers" --OPT1
    forall a:Address do
        ( dir[a].state = D_I
        | dir[a].state = D_U )
            ->
        ( MultiSetCount(i:dir[a].sharers, true) = 0 )
    endforall;

--------------------------------------------------------------------------------
-- Non-interference lemmas for parameterisation {{{
--------------------------------------------------------------------------------

--(Lemma 1): DataX can only be rcvd at node when node is owner
invariant "Lemma 1" 
    forall n:Cache do
    forall a:Address do
        (MultisetCount(i:net[n], net[n][i].mtype=DataX & net[n][i].addr=a) > 0)
            ->
        GetOwner(a) = n
    endforall
    endforall;

--(Lemma 2): Only one DataX can be in flight (per address)
invariant "Lemma 2"
    forall n:Cache do
    forall a:Address do
        (MultisetCount(i:net[n], net[n][i].mtype=DataX & net[n][i].addr=a) <= 1)
    endforall
    endforall;

--(Lemma 3): Rewrite for new restriction!
invariant "Lemma 3"
    forall n:Cache do
    forall a:Address do
    forall c:Cache do
        (MultisetCount(i:net[n], net[n][i].mtype=DataS & net[n][i].addr=a & net[n][i].src=c) = 1)
            ->
        ((forall x:Node do (MultiSetCount(i:net[x], net[x][i].mtype=GetS & net[x][i].src=c) = 0) endforall)
         & (forall x:Node do (MultiSetCount(i:net[x], net[x][i].mtype=FwdS & net[x][i].src=c) = 0) endforall)
         & (forall x:Node do (MultiSetCount(i:net[x], net[x][i].mtype=DataS & net[x][i].dst=c) = 0) endforall)
        )
    endforall
    endforall
    endforall;

--(Lemma 4): An AckC cannot be recvd except from owner
--           OR there is no other Ack in flight and the owning cache is not in WX or WS
--              OR the directory is not in WE1
invariant "Lemma 4"
    forall a:Address do
    forall c:Cache do
        (MultisetCount(i:net[Dir0], net[Dir0][i].mtype=AckC & net[Dir0][i].addr=a & net[Dir0][i].src=c) > 0)
            ->
        (GetOwner(a)=c)
        |(GetOwner(a)!=Other0 ->
            ((MultisetCount(i:net[Dir0], net[Dir0][i].mtype=AckC & net[Dir0][i].addr=a & net[Dir0][i].src!=c) = 0)
            &(caches[GetOwner(a)][a].state != C_WX)
            &(caches[GetOwner(a)][a].state != C_WS)))
        |(dir[a].state != D_WE1)
    endforall
    endforall;

--(Lemma 5): A Data cannot be recvd except from owner
--           OR there is no Ack in flight and the owning cache is not in WX or WS
--              OR the directory is not in WE1 
invariant "Lemma 5"
    forall a:Address do
    forall c:Cache do
        (MultisetCount(i:net[Dir0], net[Dir0][i].mtype=Data & net[Dir0][i].addr=a & net[Dir0][i].src=c) > 0)
            ->
        (GetOwner(a)=c)
        |(GetOwner(a)!=Other0 ->
            ((MultisetCount(i:net[Dir0], net[Dir0][i].mtype=AckC & net[Dir0][i].addr=a) = 0)
            &(caches[GetOwner(a)][a].state != C_WX)
            &(caches[GetOwner(a)][a].state != C_WS)))
        |(dir[a].state != D_WE1)
    endforall
    endforall;

--(Lemma 6): A PutE cannot be recvd except from owner
--           OR there is no Ack in flight and the owning cache is not in WX or WS
--              OR the directory is not in WE1
invariant "Lemma 6"
    forall a:Address do
    forall c:Cache do
        (MultisetCount(i:net[Dir0], net[Dir0][i].mtype=PutE & net[Dir0][i].addr=a & net[Dir0][i].src=c) > 0)
            ->
        (GetOwner(a)=c)
        |(GetOwner(a)!=Other0 ->
            ((MultisetCount(i:net[Dir0], net[Dir0][i].mtype=AckC & net[Dir0][i].addr=a) = 0)
            &(caches[GetOwner(a)][a].state != C_WX)
            &(caches[GetOwner(a)][a].state != C_WS)))
        |(dir[a].state != D_WE1)
    endforall
    endforall;

-- (Lemma 7): Cache cannot receive Data(S/X) when in D_SRO/WEn
invariant "Lemma 7"
    forall c:Cache do
    forall a:Address do
    forall c2:Cache do
        (MultiSetCount(i:net[c], net[c][i].mtype=DataX & net[c][i].addr=a & net[c][i].src=c2) > 0)
            ->
        (dir[a].state!=D_SRO & dir[a].state!=D_WEn)
    endforall
    endforall
    endforall;

-- (Lemma 8): Dir cannot receive Data in D_E/WS except from owner
invariant "Lemma 8"
    forall c:Cache do
    forall a:Address do
        (MultiSetCount(i:net[Dir0], net[Dir0][i].mtype=Data & net[Dir0][i].addr=a & net[Dir0][i].src=c) > 0)
            ->
        ((dir[a].state=D_E | dir[a].state=D_WS) -> GetOwner(a)=c)
    endforall
    endforall;

-- (Lemma 9): Cache cannot receive DataS when D_WS, unless cache is owner:
invariant "Lemma 9"
    forall c:Cache do
    forall a:Address do
        (MultiSetCount(i:net[c], net[c][i].mtype=DataX & net[c][i].addr=a) > 0)
            ->
        (dir[a].state=D_WS -> IsOwner(c,a))
    endforall
    endforall;

-- (Lemma 10): Only one AckC(1) can be in flight
invariant "Lemma 10"
    forall a:Address do
        (MultisetCount(i:net[Dir0], net[Dir0][i].mtype=AckC & net[Dir0][i].addr=a & net[Dir0][i].ack_cnt=1) <= 1)
    endforall;

-- (Lemma 11): AckC(1) only comes from owner
invariant "Lemma 11"
    forall a:Address do
    forall c:Cache do
        (MultisetCount(i:net[Dir0], net[Dir0][i].mtype=AckC & net[Dir0][i].addr=a 
                                    & net[Dir0][i].ack_cnt=1 & net[Dir0][i].src=c) > 0)
            ->
        (IsOwner(c,a))
    endforall
    endforall;

-- (Lemma 12): No Data if FwdX in flight:
invariant "Lemma 12"
    forall c:Cache do
    forall a:Address do
        (MultiSetCount(i:net[c], net[c][i].mtype=FwdX & net[c][i].addr=a
                                    & net[c][i].src!=Other0) > 0)
            ->
        (MultiSetCount(i:net[Dir0], net[Dir0][i].mtype=Data & net[Dir0][i].addr=a) = 0)
    endforall
    endforall;

-- (Lemma 13): No Data from non-owner if Put or Data are in flight
invariant "Lemma 13"
    forall c:Cache do
    forall a:Address do
        (MultiSetCount(i:net[Dir0], net[Dir0][i].src=c & net[Dir0][i].addr=a
                                & (net[Dir0][i].mtype=PutE | net[Dir0][i].mtype=Data)) > 0)
            ->
        (MultiSetCount(i:net[Dir0], net[Dir0][i].mtype=Data & net[Dir0][i].src!=c & net[Dir0][i].addr=a
                                    & !IsOwner(net[Dir0][i].src,a)) = 0)
    endforall
    endforall;


-- (Lemma 15): No Data when DataS/X in flight from Dir
invariant "Lemma 15"
    forall a:Address do
    forall c:Cache do
        (MultiSetCount(i:net[c], net[c][i].addr=a & net[c][i].src=Dir0
                                & (net[c][i].mtype=DataS | net[c][i].mtype=DataX)) > 0)
            -> 
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=Data) = 0)
    endforall
    endforall;

-- (Lemma 16): No AckC in D_WS except from owner
invariant "Lemma 16"
    forall a:Address do
    forall c:Cache do
        (dir[a].state=D_WS)
            ->
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=AckC
                                    & net[Dir0][i].src=c & !IsOwner(c,a)) = 0)
    endforall
    endforall;

-- (Lemma 17): No AckC when FwdX in flight
invariant "Lemma 17"
    forall a:Address do
    forall c:Cache do
        (MultiSetCount(i:net[c], net[c][i].addr=a & net[c][i].mtype=FwdX) > 0)
            -> 
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=AckC) = 0)
    endforall
    endforall;

-- (Lemma 18): No AckC(1) when Data in flight
invariant "Lemma 18"
    forall a:Address do
    forall c:Cache do
        (MultiSetCount(i:net[c], net[c][i].addr=a & net[c][i].mtype=Data) > 0)
            -> 
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=AckC
                                    & net[Dir0][i].ack_cnt=1) = 0)
    endforall
    endforall;

-- (Lemma 19): No AckC(1) when PutE in flight
invariant "Lemma 19"
    forall a:Address do
    forall c:Cache do
        (MultiSetCount(i:net[c], net[c][i].addr=a & net[c][i].mtype=PutE) > 0)
            -> 
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=AckC
                                    & net[Dir0][i].ack_cnt=1) = 0)
    endforall
    endforall;

-- (Lemma 20): No AckC when Data in flight in D_WE1
invariant "Lemma 20"
    forall a:Address do
    forall c:Cache do
        ((MultiSetCount(i:net[c], net[c][i].addr=a & net[c][i].mtype=Data) > 0)
            & dir[a].state=D_WE1)
            -> 
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=AckC) = 0)
    endforall
    endforall;

-- (Lemma 21): No AckC when PutE in flight in D_WE1
invariant "Lemma 21"
    forall a:Address do
    forall c:Cache do
        ((MultiSetCount(i:net[c], net[c][i].addr=a & net[c][i].mtype=PutE) > 0)
            & dir[a].state=D_WE1)
            -> 
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=AckC) = 0)
    endforall
    endforall;

-- (Lemma 22): No AckC when DataS/X in flight from Dir
invariant "Lemma 22"
    forall a:Address do
    forall c:Cache do
        (MultiSetCount(i:net[c], net[c][i].addr=a & net[c][i].src=Dir0
                                & (net[c][i].mtype=DataS | net[c][i].mtype=DataX)) > 0)
            -> 
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=AckC) = 0)
    endforall
    endforall;

-- (Lemma 23): No PutE in D_E/WS except from owner
invariant "Lemma 23"
    forall a:Address do
    forall c:Cache do
        (dir[a].state=D_WS | dir[a].state=D_E)
            ->
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=PutE
                                    & net[Dir0][i].src=c & !IsOwner(c,a)) = 0)
    endforall
    endforall;

-- (Lemma 24): No PutE when FwdX in flight
invariant "Lemma 24"
    forall a:Address do
    forall c:Cache do
        (MultiSetCount(i:net[c], net[c][i].addr=a & net[c][i].mtype=FwdX & net[c][i].src!=Other0) > 0)
            -> 
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=PutE) = 0)
    endforall
    endforall;

-- (Lemma 25): No PutE from non-owner if Put or Data are in flight
invariant "Lemma 25"
    forall c:Cache do
    forall a:Address do
        (MultiSetCount(i:net[Dir0], net[Dir0][i].src=c & net[Dir0][i].addr=a
                                & (net[Dir0][i].mtype=PutE | net[Dir0][i].mtype=Data)) > 0)
            ->
        (MultiSetCount(i:net[Dir0], net[Dir0][i].mtype=PutE & net[Dir0][i].src!=c & net[Dir0][i].addr=a
                                    & !IsOwner(net[Dir0][i].src,a)) = 0)
    endforall
    endforall;

-- (Lemma 28): No DataX in D_S/WS
invariant "Lemma 28"
    forall a:Address do
    forall c:Cache do
        (dir[a].state=D_S | dir[a].state=D_WS)
            ->
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=DataX) = 0)
    endforall
    endforall;

-- (Lemma 29): No DataX in D_U
invariant "Lemma 29"
    forall a:Address do
    forall c:Cache do
        (dir[a].state=D_U)
            ->
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=DataX) = 0)
    endforall
    endforall;

-- (Lemma 30): No DataX to c if FwdX in flight from c
invariant "Lemma 30"
    forall a:Address do
    forall c:Cache do
        (forall x:Cache do
        (MultiSetCount(i:net[x], net[x][i].addr=a & net[x][i].mtype=FwdX
                                    & net[x][i].src=c) > 0)
        endforall)
            ->
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=DataX
                                    & net[Dir0][i].dst=c) = 0)
    endforall
    endforall;

-- (Lemma 31): No DataX in D_WU1/2
invariant "Lemma 31"
    forall a:Address do
    forall c:Cache do
        (dir[a].state=D_WU1 | dir[a].state=D_WU2)
            ->
        (MultiSetCount(i:net[Dir0], net[Dir0][i].addr=a & net[Dir0][i].mtype=DataX) = 0)
    endforall
    endforall;


-- }}}

-- vim: set ft=murphi :
