package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessMatch;
import chess.ChessPiece;
import chess.Color;

public class King extends ChessPiece {

    //@ spec_public
    private final ChessMatch match;

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   requires match != null;
      @   ensures this.match == match;
      @   ensures getColor() == color;
      @   ensures getBoard() == board;
      @*/
    public King(Board board, Color color, ChessMatch match) {
        super(board, color);
        this.match = match;
    }

    /*@ public normal_behavior
      @   requires position != null;
      @   requires getBoard() != null;
      @   requires getBoard().positionExists(position);
      @   ensures \result ==>
      @       (getBoard().piece(position) == null ||
      @        ((ChessPiece)getBoard().piece(position)).getColor() != getColor());
      @   pure
      @*/
    private boolean canMove(Position position) {
        ChessPiece p = (ChessPiece) getBoard().piece(position);
        return p == null || p.getColor() != getColor();
    }

    /*@ public normal_behavior
      @   requires position != null;
      @   requires getBoard() != null;
      @   requires getBoard().positionExists(position);
      @   ensures \result ==>
      @       (getBoard().piece(position) instanceof Rook &&
      @        ((ChessPiece)getBoard().piece(position)).getColor() == getColor() &&
      @        ((ChessPiece)getBoard().piece(position)).getMoveCount() == 0);
      @   pure
      @*/
    private boolean testRookCastling(Position position) {
        ChessPiece p = (ChessPiece) getBoard().piece(position);
        return p instanceof Rook && p.getColor() == getColor() && p.getMoveCount() == 0;
    }

    /*@ also
      @ public normal_behavior
      @   requires getBoard() != null;
      @   ensures \result != null;
      @   ensures \result.length == getBoard().getRows();
      @   ensures \forall int i;
      @       0 <= i && i < getBoard().getRows() ==>
      @          \result[i].length == getBoard().getCols();
      @   pure
      @*/
    @Override
    public boolean[][] possibleMoves() {

        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];

        Position p = new Position(0, 0);

        // Acima
        p.setValues(position.getRow() - 1, position.getCol());
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Abaixo
        p.setValues(position.getRow() + 1, position.getCol());
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Esquerda
        p.setValues(position.getRow(), position.getCol() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Direita
        p.setValues(position.getRow(), position.getCol() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Noroeste
        p.setValues(position.getRow() - 1, position.getCol() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Nordeste
        p.setValues(position.getRow() - 1, position.getCol() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Sudoeste
        p.setValues(position.getRow() + 1, position.getCol() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Sudeste
        p.setValues(position.getRow() + 1, position.getCol() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Roque (castling)
        if (getMoveCount() == 0 && !match.getCheck()) {
            // Roque menor
            Position posT1 = new Position(position.getRow(), position.getCol() + 3);
            if (testRookCastling(posT1)) {
                Position p1 = new Position(position.getRow(), position.getCol() + 1);
                Position p2 = new Position(position.getRow(), position.getCol() + 2);
                if (getBoard().piece(p1) == null && getBoard().piece(p2) == null) {
                    mat[position.getRow()][position.getCol() + 2] = true;
                }
            }

            // Roque maior
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

    /*@ also
      @ public normal_behavior
      @   ensures \result.equals("K");
      @   pure
      @*/
    @Override
    public String toString() {
        return "K";
    }
}