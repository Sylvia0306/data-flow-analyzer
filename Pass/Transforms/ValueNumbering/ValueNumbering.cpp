#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/PassManager.h"

#include "llvm/Support/raw_ostream.h"

#include <vector>
#include <queue>
#include <iostream>
#include <string.h>
#include <string>
#include <sstream>
#include <stdio.h> 
#include <regex>

using namespace std;

using namespace llvm;


struct blockUnit{
  string blockName ;
  string address ; // used to store address of block
  bool changed ;
  vector <string> buffer ;
} ;

vector <blockUnit> UEVar, VarKill, LiveOut ;
vector <string> gBuffer, gBuffer_UEVar, gBuffer_VarKill, gSuc ;
vector <string> gQ ;
queue <string> gBlockName, gBlockAddress ;

int gCount = 0 ;
bool gFlag = false ;
bool forEnd =false ;

void Display( vector<string> v ) {
  for ( int i = 0 ; i < v.size() ; i++ ) {
    for ( int j = 1 ; j < v[i].length() ; j++ ) {
      errs() << v[i][j] ;
    } // for
    
    errs() << " " ;
  } // for

  errs() << "\n" ;
} // Display()

void DisplayList( vector <blockUnit> v ) {
  for ( int i = 0 ; i < v.size() ; i++ ) {
    errs() << v[i].blockName << "\n" ;
    for ( int j = 0 ; j < v[i].buffer.size() ; j++ ) {
      errs() << v[i].buffer[j] << "\n" ;
    } // fo
    errs() << "\n" ;
  } // for
} // DisplayList()

bool isInSet( vector <string> v, string str ) {
  for ( int i = 0 ; i < v.size() ; i++ ) {
    if ( v[i].compare( str ) == 0 )
      return true ;
  } // for

  return false ;
} // isInSet()

bool isInAllSet( vector <blockUnit> v, string str ) {
  // block has been add into the list
  for ( int i = 0 ; i < v.size() ; i++ ) {
    if ( v[i].blockName.compare( str ) == 0 ) {
      return true ;
    } // if
  } // for

  return false ;
} // isInSet()

bool isForEnd( string str ) {
  if ( str.compare( "\%for.end" ) == 0 )
    return true ;
  return false ;
} // isForEnd()

bool isForInc( string str ) {
  if ( str.compare( "\%for.inc" ) == 0 )
    return true ;
  return false ;
} // if

void RemoveElement( vector <string> &v, string str ) {

  for ( int i = 0 ; i < v.size() ; i += 2 ) {
    if ( v[i].compare( str ) == 0 ) {
      // find the redundant elemnt
      v.erase( v.begin() + i ) ;
      v.erase( v.begin() + i - 1 ) ;
    } // fi
  } // for
} // RemoveElement()

void setBlockName( blockUnit &uevar, blockUnit &varkill, string str ) {
  uevar.blockName = str ;
  varkill.blockName = str ;
} // setBlockName()

void setQueue( vector <string> &q, vector <string> v ) {
  for ( int i = 0 ; i < v.size() ; i++ ) {
    if ( v[i].find( "\%cmp" ) != 0  && !isInSet( q, v[i] ) && !isInAllSet( UEVar, v[i] ) ) {
      // deal with for.end for.inc case
      if ( isForInc( v[i] ) ) {
        q.push_back( v[i] ) ;
        q.push_back( "\%for.end" ) ;
      } // else if
      else {
        if ( !isForEnd( v[i] ) )
          q.push_back( v[i] ) ;
      } // else
    } // if
  } // for
} // setQueue()

void GetToken( stringstream &ss, vector<string> &temp, bool &flag ) {
  string word, word1 ;
  while ( ss >> word ) { // Extract word from the stream.
    const int length = word.length() ;
    char* char_array = new char[length + 1] ;
    // string to char array
    strcpy( char_array, word.c_str() ) ;

    int count = 0 ;
    for ( int i = 0 ; i < length ; i++ ) {
      char a = char_array[0] ;
      if( a == '%' && char_array[i] != ',' ) {
        word1 += char_array[i] ;
        if( i == length - 1 ) {
          word1 += " " ;
        } // if
      } // if
      if( char_array[i] == ',' ) {
        word1 += " " ;
      } // if
    } // for
  } // while()

  regex reg( "[%][a-z]" ) ;
  stringstream ss2( word1 ) ;
  
  while( ss2 >> word ) {
    size_t found_for = word.find( "for" );
    size_t found_while = word.find( "while" );
    size_t found_do = word.find( "do" );
    size_t found_if = word.find( "if" );
    if ( !isInSet( temp, word ) ) {
      if ( flag ) {
        // UEVar
        if ( !isInSet( gBuffer_VarKill, word ) ) {
          if ( regex_search( word, reg ) ) {
            if ( found_for != string::npos || found_while != string::npos || found_do != string::npos || found_if != string::npos )
              temp.push_back( word ) ;
            else if ( word.length() < 3 )
              temp.push_back( word ) ;
          } // if
          // temp.push_back( word ) ;
        } // if
      } // if
      else {
        // VarKill
        
        if ( regex_search( word, reg ) ) {
          if ( found_for != string::npos || found_while != string::npos || found_do != string::npos || found_if != string::npos )
            temp.push_back( word ) ;
          else if ( word.length() < 3 )
            temp.push_back( word ) ;
        } // if

        // temp.push_back( word ) ;
      } // else
    } // if
  } // while() 
} // GetToken()


void showSuccessor( string str, string name ) {
  for ( int i = 0 ; i < LiveOut.size() ; i++ ) {
    if ( LiveOut[i].address.compare( str ) == 0 ) {
      errs() << name << " successor: " << LiveOut[i].blockName << "\n" ;
    } // if
  } // for
} // showSuccessor()

int findPosOfSucBlock( string suc_address ) {
  for ( int i = 0 ; i < LiveOut.size() ; i++ ) {
    if ( LiveOut[i].address.compare( suc_address ) == 0 )
      return i ;
  } // for

  return -1 ; // if it cannot find the pos return -1
} // findPosOfBlock()

int findPosOfBlock( string blockName ) {
  for ( int i = 0 ; i < LiveOut.size() ; i++ )
    if ( LiveOut[i].blockName.compare( blockName ) == 0 )
      return i ;

  return -1 ;
} // findPosOfBlock()

int findPosOfRepeat( string str, int posBlock ) {
  for ( int i = 0 ; i < LiveOut[posBlock].buffer.size() ; i++ )
    if ( LiveOut[posBlock].buffer[i].compare( str ) == 0 )
      return i ;
    
  return -1 ;
} // findPosOfRepeat()

void killLiveOut( string blockName, int suc_pos ) {
  queue <string> killSet ;
  
  for ( int i = 0 ; i < VarKill[suc_pos].buffer.size() ; i++ ) {
    killSet.push( VarKill[suc_pos].buffer[i] ) ;
  } // for

  int posBlock = findPosOfBlock( blockName ) ;
  if ( gSuc.size() != 0 ) {
    // kill liveout element
    while ( !killSet.empty() ) {
      string str = killSet.front() ;
      for ( int i = 0 ; i < gSuc.size() ; i++ ) {
        if ( gSuc[i].compare( str ) == 0 ) {
          gSuc.erase( gSuc.begin() + i ) ;
        } // if
      } // for

      killSet.pop() ;
    } // while()
  } // if

} // killLiveOut()

void unionUE( string blockName, int suc_pos ) {
  queue <string> ueVar ;
  for ( int i = 0 ; i < UEVar[suc_pos].buffer.size() ; i++ ) {
    ueVar.push( UEVar[suc_pos].buffer[i] ) ;
  } // for

  while( !ueVar.empty() ) {
    string var = ueVar.front() ;
    if ( !isInSet( gSuc, var ) ) {
      gSuc.push_back( var ) ;
    } // if

    ueVar.pop() ;
  } // while()
} // unionUE()


void setLiveOut( string blockName, string suc_address ) {
  // blockName current basic block name
  // suc_address successor address
  int posOfSuc = findPosOfSucBlock( suc_address ) ;
  // set the suceesor live out
  gSuc = LiveOut[posOfSuc].buffer ;
  killLiveOut( blockName, posOfSuc ) ; // kill
  unionUE( blockName, posOfSuc ) ;  // union uevar

  int posOfBlock = findPosOfBlock( blockName ) ;
  for ( int i = 0 ; i < gSuc.size() ; i++ ) {
    if ( !isInSet( LiveOut[posOfBlock].buffer, gSuc[i] ) ) {
      LiveOut[posOfBlock].buffer.push_back( gSuc[i] ) ;
      LiveOut[posOfBlock].changed = true ;
    } // if
  } // for

} // setLiveOut()

bool liveOutChanged() {
  for ( int i = 0 ; i < LiveOut.size() ; i++ ) {
    if ( LiveOut[i].changed == true )
      return true ;
  } // for

  return false ;
} // liveOutChanged()

void Output() {
  // output the results
  for ( int i = 0 ; i < LiveOut.size() ; i++ ) {
    errs() << "----- " << LiveOut[i].blockName << " -----\n" ;
    errs() << "UEVAR: " ;
    Display( UEVar[i].buffer ) ;
    errs() << "VARKILL: " ;
    Display( VarKill[i].buffer ) ;
    errs() << "LIVEOUT: " ;
    Display( LiveOut[i].buffer ) ;
  } // for
} // Output()

namespace {

// This method implements what the pass does
void visitor(Function &F) {
  string func_name = "test";
	errs() << "ValueNumbering: " << F.getName() << "\n";
	
  if ( F.getName() != func_name ) 
    return;
		
  for ( auto& basic_block : F ) {
    for ( auto& inst : basic_block ) {
      // get UEVar and VarKill
      string str ;
      raw_string_ostream( str ) << inst ;
      stringstream ss(str) ;
      // errs() << inst << "\n" ;
      if ( inst.getOpcode() == Instruction::Load ) {
        // add it to the UEVar list
        // check for the VarKill list
        // if it is in the varkill list than dont add it to UEVar
        gFlag = true ;
        GetToken( ss, gBuffer_UEVar, gFlag ) ;
      } // if
      if ( inst.getOpcode() == Instruction::Store ) {
        // add it to the VarKill list
        gFlag = false ;
        GetToken( ss, gBuffer_VarKill, gFlag ) ;
      } // if
      if ( inst.isTerminator() ) {
        if ( inst.getOpcode() == Instruction::Br || inst.getOpcode() == Instruction::Ret ) {
          if ( UEVar.size() == 0 && VarKill.size() == 0 ) {
            // put entry in the buffer
            blockUnit uevar, varkill ;
            uevar.buffer = gBuffer_UEVar ;
            varkill.buffer = gBuffer_VarKill ;
            
            // set the Block name
            setBlockName( uevar, varkill, "entry" ) ;
            // push vector to each list
            UEVar.push_back( uevar ) ;
            VarKill.push_back( varkill ) ;

            gBuffer_UEVar.clear() ;
            gBuffer_VarKill.clear() ;
            GetToken( ss, gBuffer, gFlag ) ; 
            // get the first branch instruction block name
            setQueue( gQ, gBuffer ) ;
            gBuffer.clear() ;
          } // if
          else {
            blockUnit uevar, varkill ;
            uevar.buffer = gBuffer_UEVar ;
            varkill.buffer = gBuffer_VarKill ;

            // extract the block name from queue
            
            string str = gQ[0] ;
            gQ.erase( gQ.begin() ) ;
            // set the Block name
            setBlockName( uevar, varkill, str ) ;

            UEVar.push_back( uevar ) ;
            VarKill.push_back( varkill ) ;

            gBuffer_UEVar.clear() ;
            gBuffer_VarKill.clear() ;

            GetToken( ss, gBuffer, gFlag ) ; 
            // get the first branch instruction block name
            setQueue( gQ, gBuffer ) ;

            gBuffer.clear() ;
          } // else
        } // if
      } // if
    } // end for inst
  } // end for block
        
  for ( auto& basic_block : F ) {
    StringRef bbName( basic_block.getName() ) ; // basic block name
    Value *v = &basic_block ;
    stringstream ss ;
    ss << v ;
    string value = ss.str() ; // basic block address

    gBlockName.push( bbName.str() ) ;
    gBlockAddress.push( value ) ;
  } // for

  for( int i = 0 ; i < UEVar.size() ; i++ ) {
    // update the name of block and address
    string name = gBlockName.front() ;
    string address = gBlockAddress.front() ;
    gBlockName.pop() ;
    gBlockAddress.pop() ;

    UEVar[i].blockName = name ;
    VarKill[i].blockName = name ;

    UEVar[i].address = address ;
    VarKill[i].address = address ;

    // initialize LiveOut
    blockUnit tmp ;
    tmp.blockName = name ;
    tmp.address = address ;
    tmp.changed = false ;
    LiveOut.push_back( tmp ) ;
  } // while()

  bool go = true ;
  string blockName ;
  while( go ) {
    go = false ;
    for ( auto& basic_block : F ) {
      StringRef bbName( basic_block.getName() ) ; // basic block name
      // errs() << bbName.str() << "\n" ;
      for(BasicBlock* child : successors(&basic_block)) {
        stringstream ss ;
        ss << child ;
        string address = ss.str() ; // get basic block string of address
        // showSuccessor( address, bbName.str() ) ;
        setLiveOut( bbName.str(), address ) ;

        if ( liveOutChanged() ) {
          go = true ;
          int posOfBlock = findPosOfBlock( bbName.str() ) ;
          LiveOut[posOfBlock].changed = false ;
        } // if
      } // for
    } // for

  } // while()

  Output() ;
  // errs() << "UEVar" << "\n" ;
  // DisplayList( UEVar ) ;
  // errs() << "VarKill" << "\n" ;
  // DisplayList( VarKill ) ;
  // errs() << "LiveOut" << "\n" ;
  // DisplayList( LiveOut ) ;
} // visitor()


// New PM implementation
struct ValueNumberingPass : public PassInfoMixin<ValueNumberingPass> {

  // The first argument of the run() function defines on what level
  // of granularity your pass will run (e.g. Module, Function).
  // The second argument is the corresponding AnalysisManager
  // (e.g ModuleAnalysisManager, FunctionAnalysisManager)
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
  	visitor(F);
	return PreservedAnalyses::all();

	
  }
  
    static bool isRequired() { return true; }
};
}



//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------
extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {
    LLVM_PLUGIN_API_VERSION, "ValueNumberingPass", LLVM_VERSION_STRING,
    [](PassBuilder &PB) {
      PB.registerPipelineParsingCallback(
        [](StringRef Name, FunctionPassManager &FPM,
        ArrayRef<PassBuilder::PipelineElement>) {
          if(Name == "value-numbering"){
            FPM.addPass(ValueNumberingPass());
            return true;
          }
          return false;
        });
    }};
}
