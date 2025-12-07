package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessMatch;
import chess.ChessPiece;
import chess.Color;

public class Pawn extends ChessPiece {

    //@ spec_public
    private final ChessMatch match;

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   requires match != null;
      @   assignable this.*;
      @*/
    public Pawn(Board board, Color color, ChessMatch match) {
        super(board, color);
        this.match = match;
    }

    /*@ also
      @   public normal_behavior
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8; \result[i] != null && \result[i].length == 8);
      @   assignable \nothing;
      @*/
    @Override
    public boolean[][] possibleMoves() {
        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];
        Position p = new Position(0, 0);

        if (getColor() == Color.WHITE) {
            // Um para frente
            p.setValues(position.getRow() - 1, position.getCol());
            if (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
                mat[p.getRow()][p.getCol()] = true;

                // Dois para frente (primeiro movimento)
                p.setValues(position.getRow() - 2, position.getCol());
                if (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p) && getMoveCount() == 0) {
                    mat[p.getRow()][p.getCol()] = true;
                }
            }

            // Diagonal esquerda
            p.setValues(position.getRow() - 1, position.getCol() - 1);
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }

            // Diagonal direita
            p.setValues(position.getRow() - 1, position.getCol() + 1);
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }

            // En Passant Brancas
            if (position.getRow() == 3) {
                Position left = new Position(position.getRow(), position.getCol() - 1);
                if (getBoard().positionExists(left)
                        && isThereOpponentPiece(left)
                        && getBoard().piece(left) == match.getEnPassantVulnerable()) {
                    mat[left.getRow() - 1][left.getCol()] = true;
                }
                Position right = new Position(position.getRow(), position.getCol() + 1);
                if (getBoard().positionExists(right)
                        && isThereOpponentPiece(right)
                        && getBoard().piece(right) == match.getEnPassantVulnerable()) {
                    mat[right.getRow() - 1][right.getCol()] = true;
                }
            }
        } else {
            // Um para frente (pretas descem)
            p.setValues(position.getRow() + 1, position.getCol());
            if (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
                mat[p.getRow()][p.getCol()] = true;

                // Dois para frente (primeiro movimento)
                p.setValues(position.getRow() + 2, position.getCol());
                if (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p) && getMoveCount() == 0) {
                    mat[p.getRow()][p.getCol()] = true;
                }
            }

            // Diagonal esquerda (do ponto de vista das pretas)
            p.setValues(position.getRow() + 1, position.getCol() - 1);
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }

            // Diagonal direita (do ponto de vista das pretas)
            p.setValues(position.getRow() + 1, position.getCol() + 1);
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }

            // En Passant Pretas
            if (position.getRow() == 4) {
                Position left = new Position(position.getRow(), position.getCol() - 1);
                if (getBoard().positionExists(left)
                        && isThereOpponentPiece(left)
                        && getBoard().piece(left) == match.getEnPassantVulnerable()) {
                    mat[left.getRow() + 1][left.getCol()] = true;
                }
                Position right = new Position(position.getRow(), position.getCol() + 1);
                if (getBoard().positionExists(right)
                        && isThereOpponentPiece(right)
                        && getBoard().piece(right) == match.getEnPassantVulnerable()) {
                    mat[right.getRow() + 1][right.getCol()] = true;
                }
            }
        }

        return mat;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("P");
      @   pure
      @*/
    @Override
    public String toString() {
        return "P";
    }
}
