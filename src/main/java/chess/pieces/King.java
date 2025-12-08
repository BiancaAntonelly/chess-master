package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessMatch;
import chess.ChessPiece;
import chess.Color;

public class King extends ChessPiece {

    //@ spec_public
    private final /*@ non_null @*/ ChessMatch match;

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   requires match != null;
      @   ensures this.getColor() == color;
      @   ensures this.getMoveCount() == 0;
      @   ensures getBoard() == board;
      @   ensures this.match == match;
      @*/
    public King(/*@ non_null @*/ Board board,
            /*@ non_null @*/ Color color,
            /*@ non_null @*/ ChessMatch match) {
        super(board, color);
        this.match = match;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("K");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "K";
    }

    /*@ private normal_behavior
      @   requires position != null;
      @   requires getBoard().positionExists(position);
      @   ensures \result == true ==> (getBoard().piece(position) == null || 
      @           ((ChessPiece)getBoard().piece(position)).getColor() != getColor());
      @   ensures \result == false ==> (getBoard().piece(position) != null && 
      @           ((ChessPiece)getBoard().piece(position)).getColor() == getColor());
      @   assignable \nothing;
      @*/
    //@ spec_public
    private /*@ pure @*/ boolean canMove(/*@ non_null @*/ Position position) {
        ChessPiece p = (ChessPiece) getBoard().piece(position);
        return p == null || p.getColor() != getColor();
    }

    /*@ private normal_behavior
      @   requires position != null;
      @   requires getBoard().positionExists(position);
      @   ensures \result == true ==> (getBoard().piece(position) != null && 
      @           getBoard().piece(position) instanceof Rook &&
      @           ((ChessPiece)getBoard().piece(position)).getColor() == getColor() &&
      @           ((ChessPiece)getBoard().piece(position)).getMoveCount() == 0);
      @   ensures \result == false ==> (getBoard().piece(position) == null || 
      @           !(getBoard().piece(position) instanceof Rook) ||
      @           ((ChessPiece)getBoard().piece(position)).getColor() != getColor() ||
      @           ((ChessPiece)getBoard().piece(position)).getMoveCount() != 0);
      @   assignable \nothing;
      @*/
    //@ spec_public
    private /*@ pure @*/ boolean testRookCastling(/*@ non_null @*/ Position position) {
        ChessPiece p = (ChessPiece) getBoard().piece(position);
        return p != null && p instanceof Rook &&
                p.getColor() == getColor() &&
                p.getMoveCount() == 0;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8;
      @               \result[i] != null && \result[i].length == 8);
      @   assignable \nothing;
      @*/
    @Override
    public boolean[][] possibleMoves() {

        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];

        Position p = new Position(0, 0);

        // acima
        p.setValues(position.getRow() - 1, position.getCol());
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // abaixo
        p.setValues(position.getRow() + 1, position.getCol());
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // esquerda
        p.setValues(position.getRow(), position.getCol() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // direita
        p.setValues(position.getRow(), position.getCol() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // diagonal noroeste
        p.setValues(position.getRow() - 1, position.getCol() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // diagonal nordeste
        p.setValues(position.getRow() - 1, position.getCol() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // diagonal sudoeste
        p.setValues(position.getRow() + 1, position.getCol() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // diagonal sudeste
        p.setValues(position.getRow() + 1, position.getCol() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Roque
        if (getMoveCount() == 0 && !match.getCheck()) {

            // Roque pequeno (rei para a direita)
            Position posT1 = new Position(position.getRow(), position.getCol() + 3);
            if (testRookCastling(posT1)) {
                Position p1 = new Position(position.getRow(), position.getCol() + 1);
                Position p2 = new Position(position.getRow(), position.getCol() + 2);
                if (getBoard().piece(p1) == null && getBoard().piece(p2) == null) {
                    mat[position.getRow()][position.getCol() + 2] = true;
                }
            }

            // Roque grande (rei para a esquerda)
            Position posT2 = new Position(position.getRow(), position.getCol() - 4);
            if (testRookCastling(posT2)) {
                Position p1 = new Position(position.getRow(), position.getCol() - 1);
                Position p2 = new Position(position.getRow(), position.getCol() - 2);
                Position p3 = new Position(position.getRow(), position.getCol() - 3);
                if (getBoard().piece(p1) == null &&
                        getBoard().piece(p2) == null &&
                        getBoard().piece(p3) == null) {
                    mat[position.getRow()][position.getCol() - 2] = true;
                }
            }
        }

        return mat;
    }
}
