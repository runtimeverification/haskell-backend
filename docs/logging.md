# Logging

The rpc backends allow tracing of rewrites and simplifications based on contexts:

```
[Info#proxy] Starting execute request
[request 3][booster][execute][smt] Starting new SMT solver
[request 3][booster][execute][smt] Solver ready to use
[request 3][booster][execute][smt] Checking definition prelude
[request 3][booster][execute][term 58b79a1][kore-term] <generatedTop>(<foundry>(<kevm>(<k>(kseq(#execute_EVM_KItem(), VarCONTINUATION:SortK{})), <exit-code>(VarEXITCODE_CELL:SortInt{}), <mode>(NORMAL()), <schedule>(SHANGHAI_EVM()), <useGas>("false"), <ethereum>(<evm>(<output>(VarOUTPUT_CELL:SortBytes{}), <statusCode>(VarSTATUSCODE:SortStatusCode{}), <callStack>(VarCALLSTACK_CELL:SortList{}), <interimStates>(VarINTERIMSTATES_CELL:SortList{}), <touchedAccounts>(VarTOUCHEDACCOUNTS_CELL:SortSet{}), <callState>(<program>("`\128`@R4\128\NAKa\NUL\DLEW`\NUL\128\253...truncated"), <jumpDests>({"16", "87", "92", "353", "344", "365", "332", "397", "381", "296", "217", "224", "200", "205", "111", "106", "167", "162", "129", "181", "186", "143", "148", "745", "720", "618", "623", "600", "653", "686", "680", "593", "570", "575", "518", "551", "529", "452", "475", "494", "416", "431"} ), <id>(VarCONTRACT_ID:SortInt{}), <caller>(VarCALLER_ID:SortInt{}), <callData>(_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes("\156&\224\&7", _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes(#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV0_x_114b9705:SortInt{}), _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes(#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV1_y_114b9705:SortInt{}), #buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV2_z_114b9705:SortInt{}))))), <callValue>("0"), <wordStack>(.WordStack_EVM-TYPES_WordStack()), <localMem>(""), <pc>("0"), <gas>("0"), <memoryUsed>("0"), <callGas>("0"), <static>(VarSTATIC_CELL:SortBool{}), <callDepth>(VarCALLDEPTH_CELL:SortInt{})), <substate>(<selfDestruct>(VarSELFDESTRUCT_CELL:SortSet{}), <log>(VarLOG_CELL:SortList{}), <refund>("0"), <accessedAccounts>(VarACCESSEDACCOUNTS_CELL:SortSet{}), <accessedStorage>(VarACCESSEDSTORAGE_CELL:SortMap{})), <gasPrice>(VarGASPRICE_CELL:SortInt{}), <origin>(VarORIGIN_ID:SortInt{}), <blockhashes>(VarBLOCKHASHES_CELL:SortList{}), <block>(<previousHash>(VarPREVIOUSHASH_CELL:SortInt{}), <ommersHash>(VarOMMERSHASH_CELL:SortInt{}), <coinbase>(VarCOINBASE_CELL:SortInt{}), <stateRoot>(VarSTATEROOT_CELL:SortInt{}), <transactionsRoot>(VarTRANSACTIONSROOT_CELL:SortInt{}), <receiptsRoot>(VarRECEIPTSROOT_CELL:SortInt{}), <logsBloom>(VarLOGSBLOOM_CELL:SortBytes{}), <difficulty>(VarDIFFICULTY_CELL:SortInt{}), <number>(VarNUMBER_CELL:SortInt{}), <gasLimit>(VarGASLIMIT_CELL:SortInt{}), <gasUsed>(VarGASUSED_CELL:SortGas{}), <timestamp>(VarTIMESTAMP_CELL:SortInt{}), <extraData>(VarEXTRADATA_CELL:SortBytes{}), <mixHash>(VarMIXHASH_CELL:SortInt{}), <blockNonce>(VarBLOCKNONCE_CELL:SortInt{}), <baseFee>(VarBASEFEE_CELL:SortInt{}), <withdrawalsRoot>(VarWITHDRAWALSROOT_CELL:SortInt{}), <ommerBlockHeaders>(VarOMMERBLOCKHEADERS_CELL:SortJSON{}))), <network>(<chainID>(VarCHAINID_CELL:SortInt{}), <accounts>({<acctID>(VarCONTRACT_ID:SortInt{}) -> <account>(<acctID>(VarCONTRACT_ID:SortInt{}), <balance>(VarCONTRACT_BAL:SortInt{}), <code>("`\128`@R4\128\NAKa\NUL\DLEW`\NUL\128\253...truncated"), <storage>(VarCONTRACT_STORAGE:SortMap{}), <origStorage>(VarCONTRACT_ORIGSTORAGE:SortMap{}), <nonce>(VarCONTRACT_NONCE:SortInt{})), VarACCOUNTS_REST:SortAccountCellMap{}}), <txOrder>(VarTXORDER_CELL:SortList{}), <txPending>(VarTXPENDING_CELL:SortList{}), <messages>(VarMESSAGES_CELL:SortMessageCellMap{})))), <cheatcodes>(<prank>(<prevCaller>(VarPREVCALLER_CELL:SortAccount{}), <prevOrigin>(VarPREVORIGIN_CELL:SortAccount{}), <newCaller>(VarNEWCALLER_CELL:SortAccount{}), <newOrigin>(VarNEWORIGIN_CELL:SortAccount{}), <active>("false"), <depth>(VarDEPTH_CELL:SortInt{}), <singleCall>("false")), <expectedRevert>(<isRevertExpected>("false"), <expectedReason>(VarEXPECTEDREASON_CELL:SortBytes{}), <expectedDepth>(VarEXPECTEDDEPTH_CELL:SortInt{})), <expectedOpcode>(<isOpcodeExpected>("false"), <expectedAddress>(VarEXPECTEDADDRESS_CELL:SortAccount{}), <expectedValue>(VarEXPECTEDVALUE_CELL:SortInt{}), <expectedData>(VarEXPECTEDDATA_CELL:SortBytes{}), <opcodeType>(VarOPCODETYPE_CELL:SortOpcodeType{})), <expectEmit>(<recordEvent>("false"), <isEventExpected>("false"), <checkedTopics>(VarCHECKEDTOPICS_CELL:SortList{}), <checkedData>(VarCHECKEDDATA_CELL:SortBool{}), <expectedEventAddress>(VarEXPECTEDEVENTADDRESS_CELL:SortAccount{})), <whitelist>(<isCallWhitelistActive>("false"), <isStorageWhitelistActive>("false"), <addressSet>({}), <storageSlotSet>({})), <mockCalls>({})), <KEVMTracing>(<activeTracing>("false"), <traceStorage>("false"), <traceWordStack>("false"), <traceMemory>("false"), <recordedTrace>("false"), <traceData>([]))), <generatedCounter>(VarGENERATEDCOUNTER_CELL:SortInt{})) /\ notBool_(AccountCellMap:in_keys(<acctID>(VarCONTRACT_ID:SortInt{}), VarACCOUNTS_REST:SortAccountCellMap{})) /\ _<Int_(VarCALLER_ID:SortInt{}, "1461501637330902...truncated") /\ _<=Int_("0", VarCALLER_ID:SortInt{}) /\ notBool_(_andBool_(_<Int_("0", VarCALLER_ID:SortInt{}), _<=Int_(VarCALLER_ID:SortInt{}, "9"))) /\ _=/=Int_(VarCALLER_ID:SortInt{}, "6453264744265472...truncated") /\ _<=Int_("0", VarCONTRACT_BAL:SortInt{}) /\ _<Int_(VarCONTRACT_BAL:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarCONTRACT_ID:SortInt{}) /\ _<Int_(VarCONTRACT_ID:SortInt{}, "1461501637330902...truncated") /\ _=/=Int_(VarCONTRACT_ID:SortInt{}, "6453264744265472...truncated") /\ notBool_(_andBool_(_<Int_("0", VarCONTRACT_ID:SortInt{}), _<=Int_(VarCONTRACT_ID:SortInt{}, "9"))) /\ _<Int_(VarCONTRACT_NONCE:SortInt{}, "1844674407370955...truncated") /\ _<=Int_("0", VarCONTRACT_NONCE:SortInt{}) /\ _<=Int_(VarNUMBER_CELL:SortInt{}, "5789604461865809...truncated") /\ _<=Int_("0", VarNUMBER_CELL:SortInt{}) /\ _<=Int_("0", VarORIGIN_ID:SortInt{}) /\ _=/=Int_(VarORIGIN_ID:SortInt{}, "6453264744265472...truncated") /\ _<Int_(VarORIGIN_ID:SortInt{}, "1461501637330902...truncated") /\ notBool_(_andBool_(_<Int_("0", VarORIGIN_ID:SortInt{}), _<=Int_(VarORIGIN_ID:SortInt{}, "9"))) /\ _<Int_(VarTIMESTAMP_CELL:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarTIMESTAMP_CELL:SortInt{}) /\ _<Int_(VarVV0_x_114b9705:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarVV0_x_114b9705:SortInt{}) /\ _<Int_(VarVV1_y_114b9705:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarVV1_y_114b9705:SortInt{}) /\ _<Int_(VarVV2_z_114b9705:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarVV2_z_114b9705:SortInt{})
[request 3][booster][execute][term 58b79a1][rewrite UNKNOWN][detail] BASIC-BLOCK-8-TO-6
[request 3][booster][execute][term 58b79a1][rewrite UNKNOWN][match][abort] Uncertain about match with rule. Remainder: [(_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes("w\SYN\STX\247", _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes(#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", Rule#VarVV0_x_114b9705:SortInt{}), #buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", Rule#VarVV1_y_114b9705:SortInt{}))), _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes("\156&\224\&7", _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes(#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV0_x_114b9705:SortInt{}), _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes(#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV1_y_114b9705:SortInt{}), #buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV2_z_114b9705:SortInt{}))))), ({"16", "87", "92", "353", "344", "365", "332", "397", "381", "296", "217", "224", "200", "205", "111", "106", "167", "162", "129", "181", "186", "143", "148", "745", "720", "618", "623", "600", "653", "686", "680", "593", "570", "575", "518", "551", "529", "452", "475", "494", "416", "431"} , {"16", "87", "92", "353", "344", "365", "332", "397", "381", "296", "217", "224", "200", "205", "111", "106", "167", "162", "129", "181", "186", "143", "148", "745", "720", "618", "623", "600", "653", "686", "680", "593", "570", "575", "518", "551", "529", "452", "475", "494", "416", "431"} ), ({}, {}), ({}, {})]
[request 3][booster][execute][term 58b79a1][kore-term] <generatedTop>(<foundry>(<kevm>(<k>(kseq(#execute_EVM_KItem(), VarCONTINUATION:SortK{})), <exit-code>(VarEXITCODE_CELL:SortInt{}), <mode>(NORMAL()), <schedule>(SHANGHAI_EVM()), <useGas>("false"), <ethereum>(<evm>(<output>(VarOUTPUT_CELL:SortBytes{}), <statusCode>(VarSTATUSCODE:SortStatusCode{}), <callStack>(VarCALLSTACK_CELL:SortList{}), <interimStates>(VarINTERIMSTATES_CELL:SortList{}), <touchedAccounts>(VarTOUCHEDACCOUNTS_CELL:SortSet{}), <callState>(<program>("`\128`@R4\128\NAKa\NUL\DLEW`\NUL\128\253...truncated"), <jumpDests>({"16", "87", "92", "353", "344", "365", "332", "397", "381", "296", "217", "224", "200", "205", "111", "106", "167", "162", "129", "181", "186", "143", "148", "745", "720", "618", "623", "600", "653", "686", "680", "593", "570", "575", "518", "551", "529", "452", "475", "494", "416", "431"} ), <id>(VarCONTRACT_ID:SortInt{}), <caller>(VarCALLER_ID:SortInt{}), <callData>(_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes("\156&\224\&7", _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes(#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV0_x_114b9705:SortInt{}), _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes(#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV1_y_114b9705:SortInt{}), #buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV2_z_114b9705:SortInt{}))))), <callValue>("0"), <wordStack>(.WordStack_EVM-TYPES_WordStack()), <localMem>(""), <pc>("0"), <gas>("0"), <memoryUsed>("0"), <callGas>("0"), <static>(VarSTATIC_CELL:SortBool{}), <callDepth>(VarCALLDEPTH_CELL:SortInt{})), <substate>(<selfDestruct>(VarSELFDESTRUCT_CELL:SortSet{}), <log>(VarLOG_CELL:SortList{}), <refund>("0"), <accessedAccounts>(VarACCESSEDACCOUNTS_CELL:SortSet{}), <accessedStorage>(VarACCESSEDSTORAGE_CELL:SortMap{})), <gasPrice>(VarGASPRICE_CELL:SortInt{}), <origin>(VarORIGIN_ID:SortInt{}), <blockhashes>(VarBLOCKHASHES_CELL:SortList{}), <block>(<previousHash>(VarPREVIOUSHASH_CELL:SortInt{}), <ommersHash>(VarOMMERSHASH_CELL:SortInt{}), <coinbase>(VarCOINBASE_CELL:SortInt{}), <stateRoot>(VarSTATEROOT_CELL:SortInt{}), <transactionsRoot>(VarTRANSACTIONSROOT_CELL:SortInt{}), <receiptsRoot>(VarRECEIPTSROOT_CELL:SortInt{}), <logsBloom>(VarLOGSBLOOM_CELL:SortBytes{}), <difficulty>(VarDIFFICULTY_CELL:SortInt{}), <number>(VarNUMBER_CELL:SortInt{}), <gasLimit>(VarGASLIMIT_CELL:SortInt{}), <gasUsed>(VarGASUSED_CELL:SortGas{}), <timestamp>(VarTIMESTAMP_CELL:SortInt{}), <extraData>(VarEXTRADATA_CELL:SortBytes{}), <mixHash>(VarMIXHASH_CELL:SortInt{}), <blockNonce>(VarBLOCKNONCE_CELL:SortInt{}), <baseFee>(VarBASEFEE_CELL:SortInt{}), <withdrawalsRoot>(VarWITHDRAWALSROOT_CELL:SortInt{}), <ommerBlockHeaders>(VarOMMERBLOCKHEADERS_CELL:SortJSON{}))), <network>(<chainID>(VarCHAINID_CELL:SortInt{}), <accounts>({<acctID>(VarCONTRACT_ID:SortInt{}) -> <account>(<acctID>(VarCONTRACT_ID:SortInt{}), <balance>(VarCONTRACT_BAL:SortInt{}), <code>("`\128`@R4\128\NAKa\NUL\DLEW`\NUL\128\253...truncated"), <storage>(VarCONTRACT_STORAGE:SortMap{}), <origStorage>(VarCONTRACT_ORIGSTORAGE:SortMap{}), <nonce>(VarCONTRACT_NONCE:SortInt{})), VarACCOUNTS_REST:SortAccountCellMap{}}), <txOrder>(VarTXORDER_CELL:SortList{}), <txPending>(VarTXPENDING_CELL:SortList{}), <messages>(VarMESSAGES_CELL:SortMessageCellMap{})))), <cheatcodes>(<prank>(<prevCaller>(VarPREVCALLER_CELL:SortAccount{}), <prevOrigin>(VarPREVORIGIN_CELL:SortAccount{}), <newCaller>(VarNEWCALLER_CELL:SortAccount{}), <newOrigin>(VarNEWORIGIN_CELL:SortAccount{}), <active>("false"), <depth>(VarDEPTH_CELL:SortInt{}), <singleCall>("false")), <expectedRevert>(<isRevertExpected>("false"), <expectedReason>(VarEXPECTEDREASON_CELL:SortBytes{}), <expectedDepth>(VarEXPECTEDDEPTH_CELL:SortInt{})), <expectedOpcode>(<isOpcodeExpected>("false"), <expectedAddress>(VarEXPECTEDADDRESS_CELL:SortAccount{}), <expectedValue>(VarEXPECTEDVALUE_CELL:SortInt{}), <expectedData>(VarEXPECTEDDATA_CELL:SortBytes{}), <opcodeType>(VarOPCODETYPE_CELL:SortOpcodeType{})), <expectEmit>(<recordEvent>("false"), <isEventExpected>("false"), <checkedTopics>(VarCHECKEDTOPICS_CELL:SortList{}), <checkedData>(VarCHECKEDDATA_CELL:SortBool{}), <expectedEventAddress>(VarEXPECTEDEVENTADDRESS_CELL:SortAccount{})), <whitelist>(<isCallWhitelistActive>("false"), <isStorageWhitelistActive>("false"), <addressSet>({}), <storageSlotSet>({})), <mockCalls>({})), <KEVMTracing>(<activeTracing>("false"), <traceStorage>("false"), <traceWordStack>("false"), <traceMemory>("false"), <recordedTrace>("false"), <traceData>([]))), <generatedCounter>(VarGENERATEDCOUNTER_CELL:SortInt{})) /\ notBool_(AccountCellMap:in_keys(<acctID>(VarCONTRACT_ID:SortInt{}), VarACCOUNTS_REST:SortAccountCellMap{})) /\ _<Int_(VarCALLER_ID:SortInt{}, "1461501637330902...truncated") /\ _<=Int_("0", VarCALLER_ID:SortInt{}) /\ notBool_(_andBool_(_<Int_("0", VarCALLER_ID:SortInt{}), _<=Int_(VarCALLER_ID:SortInt{}, "9"))) /\ _=/=Int_(VarCALLER_ID:SortInt{}, "6453264744265472...truncated") /\ _<=Int_("0", VarCONTRACT_BAL:SortInt{}) /\ _<Int_(VarCONTRACT_BAL:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarCONTRACT_ID:SortInt{}) /\ _<Int_(VarCONTRACT_ID:SortInt{}, "1461501637330902...truncated") /\ _=/=Int_(VarCONTRACT_ID:SortInt{}, "6453264744265472...truncated") /\ notBool_(_andBool_(_<Int_("0", VarCONTRACT_ID:SortInt{}), _<=Int_(VarCONTRACT_ID:SortInt{}, "9"))) /\ _<Int_(VarCONTRACT_NONCE:SortInt{}, "1844674407370955...truncated") /\ _<=Int_("0", VarCONTRACT_NONCE:SortInt{}) /\ _<=Int_(VarNUMBER_CELL:SortInt{}, "5789604461865809...truncated") /\ _<=Int_("0", VarNUMBER_CELL:SortInt{}) /\ _<=Int_("0", VarORIGIN_ID:SortInt{}) /\ _=/=Int_(VarORIGIN_ID:SortInt{}, "6453264744265472...truncated") /\ _<Int_(VarORIGIN_ID:SortInt{}, "1461501637330902...truncated") /\ notBool_(_andBool_(_<Int_("0", VarORIGIN_ID:SortInt{}), _<=Int_(VarORIGIN_ID:SortInt{}, "9"))) /\ _<Int_(VarTIMESTAMP_CELL:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarTIMESTAMP_CELL:SortInt{}) /\ _<Int_(VarVV0_x_114b9705:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarVV0_x_114b9705:SortInt{}) /\ _<Int_(VarVV1_y_114b9705:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarVV1_y_114b9705:SortInt{}) /\ _<Int_(VarVV2_z_114b9705:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarVV2_z_114b9705:SortInt{})
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][kore-term] <generatedTop>(<foundry>(<kevm>(<k>(kseq(#execute_EVM_KItem(), VarCONTINUATION:SortK{})), <exit-code>(VarEXITCODE_CELL:SortInt{}), <mode>(NORMAL()), <schedule>(SHANGHAI_EVM()), <useGas>("false"), <ethereum>(<evm>(<output>(VarOUTPUT_CELL:SortBytes{}), <statusCode>(VarSTATUSCODE:SortStatusCode{}), <callStack>(VarCALLSTACK_CELL:SortList{}), <interimStates>(VarINTERIMSTATES_CELL:SortList{}), <touchedAccounts>(VarTOUCHEDACCOUNTS_CELL:SortSet{}), <callState>(<program>("`\128`@R4\128\NAKa\NUL\DLEW`\NUL\128\253...truncated"), <jumpDests>({"16", "87", "92", "353", "344", "365", "332", "397", "381", "296", "217", "224", "200", "205", "111", "106", "167", "162", "129", "181", "186", "143", "148", "745", "720", "618", "623", "600", "653", "686", "680", "593", "570", "575", "518", "551", "529", "452", "475", "494", "416", "431"} ), <id>(VarCONTRACT_ID:SortInt{}), <caller>(VarCALLER_ID:SortInt{}), <callData>(_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes("\156&\224\&7", _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes(#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV0_x_114b9705:SortInt{}), _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes(#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV1_y_114b9705:SortInt{}), #buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV2_z_114b9705:SortInt{}))))), <callValue>("0"), <wordStack>(.WordStack_EVM-TYPES_WordStack()), <localMem>(""), <pc>("0"), <gas>("0"), <memoryUsed>("0"), <callGas>("0"), <static>(VarSTATIC_CELL:SortBool{}), <callDepth>(VarCALLDEPTH_CELL:SortInt{})), <substate>(<selfDestruct>(VarSELFDESTRUCT_CELL:SortSet{}), <log>(VarLOG_CELL:SortList{}), <refund>("0"), <accessedAccounts>(VarACCESSEDACCOUNTS_CELL:SortSet{}), <accessedStorage>(VarACCESSEDSTORAGE_CELL:SortMap{})), <gasPrice>(VarGASPRICE_CELL:SortInt{}), <origin>(VarORIGIN_ID:SortInt{}), <blockhashes>(VarBLOCKHASHES_CELL:SortList{}), <block>(<previousHash>(VarPREVIOUSHASH_CELL:SortInt{}), <ommersHash>(VarOMMERSHASH_CELL:SortInt{}), <coinbase>(VarCOINBASE_CELL:SortInt{}), <stateRoot>(VarSTATEROOT_CELL:SortInt{}), <transactionsRoot>(VarTRANSACTIONSROOT_CELL:SortInt{}), <receiptsRoot>(VarRECEIPTSROOT_CELL:SortInt{}), <logsBloom>(VarLOGSBLOOM_CELL:SortBytes{}), <difficulty>(VarDIFFICULTY_CELL:SortInt{}), <number>(VarNUMBER_CELL:SortInt{}), <gasLimit>(VarGASLIMIT_CELL:SortInt{}), <gasUsed>(VarGASUSED_CELL:SortGas{}), <timestamp>(VarTIMESTAMP_CELL:SortInt{}), <extraData>(VarEXTRADATA_CELL:SortBytes{}), <mixHash>(VarMIXHASH_CELL:SortInt{}), <blockNonce>(VarBLOCKNONCE_CELL:SortInt{}), <baseFee>(VarBASEFEE_CELL:SortInt{}), <withdrawalsRoot>(VarWITHDRAWALSROOT_CELL:SortInt{}), <ommerBlockHeaders>(VarOMMERBLOCKHEADERS_CELL:SortJSON{}))), <network>(<chainID>(VarCHAINID_CELL:SortInt{}), <accounts>({<acctID>(VarCONTRACT_ID:SortInt{}) -> <account>(<acctID>(VarCONTRACT_ID:SortInt{}), <balance>(VarCONTRACT_BAL:SortInt{}), <code>("`\128`@R4\128\NAKa\NUL\DLEW`\NUL\128\253...truncated"), <storage>(VarCONTRACT_STORAGE:SortMap{}), <origStorage>(VarCONTRACT_ORIGSTORAGE:SortMap{}), <nonce>(VarCONTRACT_NONCE:SortInt{})), VarACCOUNTS_REST:SortAccountCellMap{}}), <txOrder>(VarTXORDER_CELL:SortList{}), <txPending>(VarTXPENDING_CELL:SortList{}), <messages>(VarMESSAGES_CELL:SortMessageCellMap{})))), <cheatcodes>(<prank>(<prevCaller>(VarPREVCALLER_CELL:SortAccount{}), <prevOrigin>(VarPREVORIGIN_CELL:SortAccount{}), <newCaller>(VarNEWCALLER_CELL:SortAccount{}), <newOrigin>(VarNEWORIGIN_CELL:SortAccount{}), <active>("false"), <depth>(VarDEPTH_CELL:SortInt{}), <singleCall>("false")), <expectedRevert>(<isRevertExpected>("false"), <expectedReason>(VarEXPECTEDREASON_CELL:SortBytes{}), <expectedDepth>(VarEXPECTEDDEPTH_CELL:SortInt{})), <expectedOpcode>(<isOpcodeExpected>("false"), <expectedAddress>(VarEXPECTEDADDRESS_CELL:SortAccount{}), <expectedValue>(VarEXPECTEDVALUE_CELL:SortInt{}), <expectedData>(VarEXPECTEDDATA_CELL:SortBytes{}), <opcodeType>(VarOPCODETYPE_CELL:SortOpcodeType{})), <expectEmit>(<recordEvent>("false"), <isEventExpected>("false"), <checkedTopics>(VarCHECKEDTOPICS_CELL:SortList{}), <checkedData>(VarCHECKEDDATA_CELL:SortBool{}), <expectedEventAddress>(VarEXPECTEDEVENTADDRESS_CELL:SortAccount{})), <whitelist>(<isCallWhitelistActive>("false"), <isStorageWhitelistActive>("false"), <addressSet>({}), <storageSlotSet>({})), <mockCalls>({})), <KEVMTracing>(<activeTracing>("false"), <traceStorage>("false"), <traceWordStack>("false"), <traceMemory>("false"), <recordedTrace>("false"), <traceData>([]))), <generatedCounter>(VarGENERATEDCOUNTER_CELL:SortInt{})) /\ notBool_(AccountCellMap:in_keys(<acctID>(VarCONTRACT_ID:SortInt{}), VarACCOUNTS_REST:SortAccountCellMap{})) /\ _<Int_(VarCALLER_ID:SortInt{}, "1461501637330902...truncated") /\ _<=Int_("0", VarCALLER_ID:SortInt{}) /\ notBool_(_andBool_(_<Int_("0", VarCALLER_ID:SortInt{}), _<=Int_(VarCALLER_ID:SortInt{}, "9"))) /\ _=/=Int_(VarCALLER_ID:SortInt{}, "6453264744265472...truncated") /\ _<=Int_("0", VarCONTRACT_BAL:SortInt{}) /\ _<Int_(VarCONTRACT_BAL:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarCONTRACT_ID:SortInt{}) /\ _<Int_(VarCONTRACT_ID:SortInt{}, "1461501637330902...truncated") /\ _=/=Int_(VarCONTRACT_ID:SortInt{}, "6453264744265472...truncated") /\ notBool_(_andBool_(_<Int_("0", VarCONTRACT_ID:SortInt{}), _<=Int_(VarCONTRACT_ID:SortInt{}, "9"))) /\ _<Int_(VarCONTRACT_NONCE:SortInt{}, "1844674407370955...truncated") /\ _<=Int_("0", VarCONTRACT_NONCE:SortInt{}) /\ _<=Int_(VarNUMBER_CELL:SortInt{}, "5789604461865809...truncated") /\ _<=Int_("0", VarNUMBER_CELL:SortInt{}) /\ _<=Int_("0", VarORIGIN_ID:SortInt{}) /\ _=/=Int_(VarORIGIN_ID:SortInt{}, "6453264744265472...truncated") /\ _<Int_(VarORIGIN_ID:SortInt{}, "1461501637330902...truncated") /\ notBool_(_andBool_(_<Int_("0", VarORIGIN_ID:SortInt{}), _<=Int_(VarORIGIN_ID:SortInt{}, "9"))) /\ _<Int_(VarTIMESTAMP_CELL:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarTIMESTAMP_CELL:SortInt{}) /\ _<Int_(VarVV0_x_114b9705:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarVV0_x_114b9705:SortInt{}) /\ _<Int_(VarVV1_y_114b9705:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarVV1_y_114b9705:SortInt{}) /\ _<Int_(VarVV2_z_114b9705:SortInt{}, "1157920892373161...truncated") /\ _<=Int_("0", VarVV2_z_114b9705:SortInt{})
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][term 24777d8][kore-term] <generatedTop>(<foundry>(<kevm>(<k>(kseq(#execute_EVM_KItem(), VarCONTINUATION:SortK{})), <exit-code>(VarEXITCODE_CELL:SortInt{}), <mode>(NORMAL()), <schedule>(SHANGHAI_EVM()), <useGas>("false"), <ethereum>(<evm>(<output>(VarOUTPUT_CELL:SortBytes{}), <statusCode>(VarSTATUSCODE:SortStatusCode{}), <callStack>(VarCALLSTACK_CELL:SortList{}), <interimStates>(VarINTERIMSTATES_CELL:SortList{}), <touchedAccounts>(VarTOUCHEDACCOUNTS_CELL:SortSet{}), <callState>(<program>("`\128`@R4\128\NAKa\NUL\DLEW`\NUL\128\253...truncated"), <jumpDests>({"16", "87", "92", "353", "344", "365", "332", "397", "381", "296", "217", "224", "200", "205", "111", "106", "167", "162", "129", "181", "186", "143", "148", "745", "720", "618", "623", "600", "653", "686", "680", "593", "570", "575", "518", "551", "529", "452", "475", "494", "416", "431"} ), <id>(VarCONTRACT_ID:SortInt{}), <caller>(VarCALLER_ID:SortInt{}), <callData>(_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes("\156&\224\&7", _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes(#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV0_x_114b9705:SortInt{}), _+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes(#buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV1_y_114b9705:SortInt{}), #buf(_,_)_BUF-SYNTAX_Bytes_Int_Int("32", VarVV2_z_114b9705:SortInt{}))))), <callValue>("0"), <wordStack>(.WordStack_EVM-TYPES_WordStack()), <localMem>(""), <pc>("0"), <gas>("0"), <memoryUsed>("0"), <callGas>("0"), <static>(VarSTATIC_CELL:SortBool{}), <callDepth>(VarCALLDEPTH_CELL:SortInt{})), <substate>(<selfDestruct>(VarSELFDESTRUCT_CELL:SortSet{}), <log>(VarLOG_CELL:SortList{}), <refund>("0"), <accessedAccounts>(VarACCESSEDACCOUNTS_CELL:SortSet{}), <accessedStorage>(VarACCESSEDSTORAGE_CELL:SortMap{})), <gasPrice>(VarGASPRICE_CELL:SortInt{}), <origin>(VarORIGIN_ID:SortInt{}), <blockhashes>(VarBLOCKHASHES_CELL:SortList{}), <block>(<previousHash>(VarPREVIOUSHASH_CELL:SortInt{}), <ommersHash>(VarOMMERSHASH_CELL:SortInt{}), <coinbase>(VarCOINBASE_CELL:SortInt{}), <stateRoot>(VarSTATEROOT_CELL:SortInt{}), <transactionsRoot>(VarTRANSACTIONSROOT_CELL:SortInt{}), <receiptsRoot>(VarRECEIPTSROOT_CELL:SortInt{}), <logsBloom>(VarLOGSBLOOM_CELL:SortBytes{}), <difficulty>(VarDIFFICULTY_CELL:SortInt{}), <number>(VarNUMBER_CELL:SortInt{}), <gasLimit>(VarGASLIMIT_CELL:SortInt{}), <gasUsed>(VarGASUSED_CELL:SortGas{}), <timestamp>(VarTIMESTAMP_CELL:SortInt{}), <extraData>(VarEXTRADATA_CELL:SortBytes{}), <mixHash>(VarMIXHASH_CELL:SortInt{}), <blockNonce>(VarBLOCKNONCE_CELL:SortInt{}), <baseFee>(VarBASEFEE_CELL:SortInt{}), <withdrawalsRoot>(VarWITHDRAWALSROOT_CELL:SortInt{}), <ommerBlockHeaders>(VarOMMERBLOCKHEADERS_CELL:SortJSON{}))), <network>(<chainID>(VarCHAINID_CELL:SortInt{}), <accounts>({<acctID>(VarCONTRACT_ID:SortInt{}) -> <account>(<acctID>(VarCONTRACT_ID:SortInt{}), <balance>(VarCONTRACT_BAL:SortInt{}), <code>("`\128`@R4\128\NAKa\NUL\DLEW`\NUL\128\253...truncated"), <storage>(VarCONTRACT_STORAGE:SortMap{}), <origStorage>(VarCONTRACT_ORIGSTORAGE:SortMap{}), <nonce>(VarCONTRACT_NONCE:SortInt{})), VarACCOUNTS_REST:SortAccountCellMap{}}), <txOrder>(VarTXORDER_CELL:SortList{}), <txPending>(VarTXPENDING_CELL:SortList{}), <messages>(VarMESSAGES_CELL:SortMessageCellMap{})))), <cheatcodes>(<prank>(<prevCaller>(VarPREVCALLER_CELL:SortAccount{}), <prevOrigin>(VarPREVORIGIN_CELL:SortAccount{}), <newCaller>(VarNEWCALLER_CELL:SortAccount{}), <newOrigin>(VarNEWORIGIN_CELL:SortAccount{}), <active>("false"), <depth>(VarDEPTH_CELL:SortInt{}), <singleCall>("false")), <expectedRevert>(<isRevertExpected>("false"), <expectedReason>(VarEXPECTEDREASON_CELL:SortBytes{}), <expectedDepth>(VarEXPECTEDDEPTH_CELL:SortInt{})), <expectedOpcode>(<isOpcodeExpected>("false"), <expectedAddress>(VarEXPECTEDADDRESS_CELL:SortAccount{}), <expectedValue>(VarEXPECTEDVALUE_CELL:SortInt{}), <expectedData>(VarEXPECTEDDATA_CELL:SortBytes{}), <opcodeType>(VarOPCODETYPE_CELL:SortOpcodeType{})), <expectEmit>(<recordEvent>("false"), <isEventExpected>("false"), <checkedTopics>(VarCHECKEDTOPICS_CELL:SortList{}), <checkedData>(VarCHECKEDDATA_CELL:SortBool{}), <expectedEventAddress>(VarEXPECTEDEVENTADDRESS_CELL:SortAccount{})), <whitelist>(<isCallWhitelistActive>("false"), <isStorageWhitelistActive>("false"), <addressSet>({}), <storageSlotSet>({})), <mockCalls>({})), <KEVMTracing>(<activeTracing>("false"), <traceStorage>("false"), <traceWordStack>("false"), <traceMemory>("false"), <recordedTrace>("false"), <traceData>([]))), <generatedCounter>(VarGENERATEDCOUNTER_CELL:SortInt{}))
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][term 24777d8][function 00be500][detail] ...kproj/evm-semantics/buf.md :  (49, 10)
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][term 24777d8][function 00be500][failure] Concreteness constraint violated: term has variables
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][term 24777d8][function d38a123][detail] ...kproj/evm-semantics/buf.md :  (52, 10)
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][term 24777d8][function d38a123][failure] Concreteness constraint violated: term has variables
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][term 24777d8][simplification 5a8ecf6][detail] BYTES-SIMPLIFICATION.buf-asWord-invert-lr-len-gt
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][term 24777d8][simplification 5a8ecf6][match][failure] Uncertain about match with rule. Remainder: [(#asWord(_)_EVM-TYPES_Int_Bytes(Eq#VarB:SortBytes{}), VarVV0_x_114b9705:SortInt{})]
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][term 24777d8][simplification 4ec7f53][detail] BYTES-SIMPLIFICATION.buf-asWord-invert-lr-len-leq
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][term 24777d8][simplification 4ec7f53][match][failure] Uncertain about match with rule. Remainder: [(#asWord(_)_EVM-TYPES_Int_Bytes(Eq#VarB:SortBytes{}), VarVV0_x_114b9705:SortInt{})]
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][term 24777d8][function 00be500][detail] ...kproj/evm-semantics/buf.md :  (49, 10)
[request 3][booster][execute][term 58b79a1][simplify][term 58b79a1][term 24777d8][function 00be500][failure] Concreteness constraint violated: term has variables
```

## Logging contexts

The log contexts should allow the reader to reconstruct how execution proceeded within the two backends. Note however that due to the different architectures of the two backends, the logs will not always have the same structure.

### `[request n][booster]`/ `[request n][kore]`/ `[proxy]`
Top level contexts indicating the current request being computed in the given backend.

### `[ceil]`

Context showing the ceil/definedness analysis of rules at load-time. See below for the structure of the emmited infromation:

```
[ceil][rewrite d76d278][detail] ...kproj/evm-semantics/evm.md :  (1822, 10)
[ceil][rewrite d76d278][partial-symbols] Lbl#point(_)_EVM_Bytes_G1Point, LblBN128Add(_,_)_KRYPTO_G1Point_G1Point_G1Point
[ceil][rewrite d76d278][computed-ceils] #Ceil( isValidPoint(_)_KRYPTO_Bool_G1Point(Rule#VarP1:SortG1Point{}) ), #Ceil( #point(_)_EVM_Bytes_G1Point(BN128Add(_,_)_KRYPTO_G1Point_G1Point_G1Point(Rule#VarP1:SortG1Point{}, Rule#VarP2:SortG1Point{})) ), #Ceil( isValidPoint(_)_KRYPTO_Bool_G1Point(Rule#VarP2:SortG1Point{}) )
[ceil][simplification 5c9073a][detail] ...evm-semantics/lemmas/lemmas.k :  (178, 10)
[ceil][simplification 5c9073a][partial-symbols] Lbl_modInt_
```

### `[execute]`/`[add-module]`/`[get-model]`
top-level (right below `[booster]`/`[kore]`) contexts corresponding to rpc calls

### `[term <hash>]`
nested context tying any logs within to a particular term. We use the internal hash of a term and pretty print each new term inside a `[kore-term]` context, e.g.: 
```
...[term 2749139][kore-term] _<Int_(VarCALLER_ID:SortInt{}, "1461501637330902...truncated")
```
then we can have e.g. 
```
...[term 2749139][simplification 772d650][match][failure] Symbols differ: minInt(_,_)_INT-COMMON_Int_Int_Int(Eq#VarB:SortInt{}, Eq#VarC:SortInt{}) "1461501637330902...truncated"
```

### `[simplify]`
top-level or nested context signifying the simplification phase of the whole configuration, either when a simplify request is received i.e. context `[booster][simplify]` or inside the execute request when unification is unclear and the booster attempts to simplify the configuration before re-trying to apply rewrite rules: 
```
...[booster][execute][term 58b79a1][simplify]...
```

### `[rewrite <hash>]`/`[simplification <hash>]`/`[function <hash>]`
signifies we are in a context of attempting to apply a rewrite/simplification/function rule. The `<hash>` used is the rule's unique id, truncated to the first 7 letters. We also emit a nested `[detail]` context, specifying the rule label/location for convenience: 
```
...[simplification b67b7ce][detail] ...evm-semantics/lemmas/lemmas.k :  (217, 10)
```

### `[constraint]`
nested context, signifying evaluation/simplification of a constraint, usually a `requires` clause of a rule.

### `[match]`/`[match][RESULT]`
nested context, for  running the matching algorithm. `RESULT` can be `success`, `failure`, or `indeterminate`. Typical log lines:
```
...[match][success] Substitution: Eq#VarB:SortBool{} -> _==Int_("1997931255"...
...[match][failure] Uncertain about match with rule. Remainder: [(_==Int_(Eq#VarX:SortInt{}, "0"), ...
...[match][indeterminate] Uncertain about match with rule. Remainder: [(PUSH(_)_EVM_PushOp_Int(Rule#VarN:SortInt{}),#next(...))...
...[match][abort] Uncertain about match with rule. Remainder: [(PUSH(_)_EVM_PushOp_Int(Rule#VarN:SortInt{}),...)...
```

### `[failure]`/`[STAGE][abort]` (for `rewrite` rules)
All of the above contexts indicate some for of a failure. Roughly speaking, `[failure]` is an indicator that a rewrite rule does not apply, whereas an `[abort]` is usually indicative of the booster being unable/unsure about proceeding and falls back to the old backend.  
The reason to abort is usually indicated by a `STAGE` context before `abort`, which can be `match`, `definedness`, or `constraint`.

### `[failure][continue]`/`[failure][break]` (for equations)
Things get more complicated in equation application, where some failures are recoverable from depending on the type of equation being applied. We indicate these with a nested `[failure][continue]` context, indicating that the backend will proceed applying further rules in the same priority group. If a failure to apply an equation leads to simplification aborting entirely, we use the `[failure][break]` context to show the reason.

### `[success]` / `[success][cached]`
context used for printing successful match or rewrite. will usually have the following shapes:

rewritten one term into another: 

```
...[term 6b25517][success][term c75f0d1][kore-term] ...
...[term 585d8c3][llvm][success][term 98b0892][kore-term] "true"
```

rewritten one term into another using a cached result: 

```
...[term 6b25517][success][cached][term c75f0d1][kore-term] ...
```

rewritten a subterm inside a term:

```
...[simplify][term cf6a9a6][term 42b88c6][llvm][success][term 6c1e8f3][kore-term]...
```

succesfully matched:
```
...[match][success] Substitution: Eq#VarB1:SortBytes{} -> "\156&\224\&7" , ...
```


### `[smt]`
nested context for any smt operations

```
...[booster][execute][term 8d61dc1][rewrite e3b68cc][smt] Predicates to check: _<Int_(VarCONTRACT_BAL:SortInt{}, "0")
...[booster][execute][term 8d61dc1][rewrite e3b68cc][smt] Check of Given ∧ P and Given ∧ !P produced (Unsat,Sat)
```

### `[llvm]`
log any calls to the llvm simplifier here. usually it will be of the form:

```
...[constraint][term 585d8c3][kore-term] _<=Int_("0", "32")
...[constraint][term 585d8c3][llvm][success][term 98b0892][kore-term] "true"
```

### `[error]`
log any internal errors (usually aborts a request with an error message).

## Context filtering


To turn on context logging, use the `--log-context` flag to select which of the above contexts to emit. The expression, accepted by this flag has the following features:

* `foo` - match context `foo` eactly
* `foo*` - match context with the prefix `foo`, e.g. `simplification a*` will match the context `[simplification aa89f12]`
* `*foo` - match context with the suffix `foo`
* `*foo*` - match context with the infix `foo`
* `!foo*` - don't match `foo`
* `foo|bar` - match `foo` or `bar` context, e.g. `kore|booster`
* `foo&bar` - match `foo` and `bar` context, most likely used with negation e.g. `!kore&!proxy`
* `foo,bar` - match a context `foo` with an immediately nested context `bar`
* `foo>bar` - match a context `foo` with a child context `bar`
* `foo>bar.` - match a context `foo` with a child context `bar` which is the last context, e.g. the context `[foo][baz][bar]` would match but `[foo][bar][baz]` does not.

Other allowed expressions:

* `(foo|bar)&!baz`
* `!(foo|bar)`


Here are some common patterns we may want to use:

* `request*,kore|booster` - log everything from kore and booster
* `request*,kore|booster>!(kore-term|detail).` - log everything from kore and booster except for the innermost `kore-term` or `detail` contexts, which contain the pretty printed terms and extra details about e.g. rule locations which may be too noisy.
* `request*,kore|booster>simplification*` - log every simplification rule attempt from kore and booster
* `request*,kore|booster>simplification*|equation*` - log every simplification and function application attempt from kore and booster
* `ceil>partial-symbols.` - log a minimal ceil analysis showing all the rules which contain partial symbols on the RHS and aren't marked as preserving definedness

## Timestamps

The booster now supports timestamps via `--log-timestamps` where the timestamp format can be specified as `--timestamp-format nanosecond` or `--timestamp-format pretty`


## Common log context sets

To make it easier for users to get started with log contexts and/or to collect a specific subset of context logs required for certain utilities, such as the `time-profile` or `count-aborts` tool, we support the following "log levels", which can be set via the `-l <Level>` flag when starting an rpc server:

| Log level        | Description                                                                                                  |
|------------------|--------------------------------------------------------------------------------------------------------------|
| Aborts           | Log information related to aborting execution                                                                |
| Rewrite          | Log all rewriting in booster                                                                                 |
| RewriteSuccess   | Log successful rewrites (booster and kore-rpc)                                                               |
| Simplify         | Log all simplification/evaluation in booster                                                                 |
| SimplifySuccess  | Log successful simplifications (booster and kore-rpc)                                                        |
| SMT              | Log the SMT-solver interactions                                                                              |
| EquationWarnings | Log warnings indicating soft-violations of conditions, i.e. exceeding the equation recursion/iteration limit |
| TimeProfile      | Logs for timing analysis (to be used by the `time-profile` tool)                                             |
| Timing           | Printis beasic timing stats per request; formerly the `--print-stats` flag in booster server                 |

_Note: To see what context filters these levels correspond too, see the `Booster.CLOptions` module, specifically the `levelToContext` map._