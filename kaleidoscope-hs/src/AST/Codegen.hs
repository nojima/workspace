module AST.Codegen where

import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.ByteString.Short qualified as ByteString.Short
import Data.Map (Map)
import Data.Map qualified as Map

import Control.Monad.State (State, MonadState)
import Control.Monad.State qualified as State

import LLVM.AST qualified as LLVM
import LLVM.AST.Global qualified as LLVM
import LLVM.AST.Linkage qualified as Linkage
import LLVM.AST.Constant qualified as Constant
import LLVM.AST.Attribute qualified as Attribute
import LLVM.AST.CallingConvention qualified as Convention
import LLVM.AST.FloatingPointPredicate as FloatingPoint

import AST.Syntax (Expr, BinOp)
import AST.Syntax qualified as Syntax

-------------------------------------------------------------------------------

double :: LLVM.Type
double = LLVM.FloatingPointType LLVM.DoubleFP

-------------------------------------------------------------------------------

type Names = Map ByteString Int

type SymbolTable = Map ByteString LLVM.Operand

data CodegenState = CodegenState
  { currentBlock :: LLVM.Name                -- Name of the active block to append to
  , blocks       :: Map LLVM.Name BlockState -- Blocks for function
  , symbols      :: SymbolTable              -- Function scope symbol table
  , blockCount   :: Int                      -- Count of basic blocks
  , count        :: Word                     -- Count of unnamed instructions
  , names        :: Names                    -- Name Supply
  }
  deriving Show

data BlockState = BlockState
  { idx :: Int                                  -- Block index
  , stack :: [LLVM.Named LLVM.Instruction]      -- Stack of instructions
  , term  :: Maybe (LLVM.Named LLVM.Terminator) -- Block terminator
  }
  deriving Show

newtype Codegen a = Codegen (State CodegenState a)
  deriving (Functor, Applicative, Monad, MonadState CodegenState)

newtype LLVMState a = LLVMState (State LLVM.Module a)
  deriving (Functor, Applicative, Monad, MonadState LLVM.Module)

runLLVM :: LLVM.Module -> LLVMState a -> LLVM.Module
runLLVM mod (LLVMState llvm) = State.execState llvm mod

emptyModule :: ByteString -> LLVM.Module
emptyModule label = LLVM.defaultModule
  { LLVM.moduleName = ByteString.Short.toShort label
  }
