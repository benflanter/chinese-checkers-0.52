using System;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.InteropServices.WindowsRuntime;
using System.Security.Cryptography;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using System.Windows.Forms;
using static System.Windows.Forms.VisualStyles.VisualStyleElement.ProgressBar;


namespace ChineseCheckers.Model
{
    public class ComputerPlayer : Player
    {
        private enum State { START = 1, MIDDLE, END };
        private Dictionary<int, Piece> origins;
        private Dictionary<int, Piece> destinations;
        private Piece outsidePiece;
        private int outsidePieces = 0;
        private int countEnd = 0, countMid = 0;
        private int prioritiyPoint = 5;
        private int rearMostPoint = 15;
        private int destPoint = 40;
        private int compressionPoint = 300;
        private int avoidPoint = -1000;
        private int devFactor = 150;
        private int averageRow;
        private int SMovePoint;
        private int belowAvgFactor = 4;
        private int rearMostKey;
        private int[,] weights =
        {
            { 0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,0,0,100,0,100,0,0,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,0,100,0,100,0,100,0,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,100,0,100,0,100,0,100,0,0,0,0,0,0,0,0,0 },
            { -100,0,-60,0,-50,0,75,0,85,0,90,0,90,0,90,0,85,0,75,0,-50,0,-60,0,-100 },
            { 0,-50,0,-30,0,55,0,75,0,80,0,80,0,80,0,80,0,75,0,55,0,-30,0,-50,0 },
            { 0,0,-25,0,-20,0,55,0,65,0,70,0,70,0,70,0,65,0,55,0,-20,0,-25,0,0 },
            { 0,0,0,-15,0,-10,0,50,0,55,0,60,0,60,0,55,0,50,0,-10,0,-15,0,0,0 },
            { 0,0,0,0,-5,0,15,0,40,0,50,0,50,0,40,0,40,0,15,0,-5,0,0,0,0 },
            { 0,0,0,-5,0,10,0,30,0,40,0,40,0,40,0,40,0,30,0,10,0,-5,0,0,0 },
            { 0,0,-10,0,1,0,8,0,25,0,30,0,30,0,30,0,25,0,8,0,1,0,-10,0,0 },
            { 0,1,0,3,0,3,0,15,0,20,0,20,0,20,0,20,0,15,0,3,0,3,0,1,0 },
            { 1,0,1,0,1,0,5,0,10,0,10,0,10,0,10,0,10,0,5,0,1,0,1,0,1 },
            { 0,0,0,0,0,0,0,0,0,5,0,5,0,5,0,5,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,0,3,0,3,0,3,0,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0 },
        };

        public ComputerPlayer(bool side, Board board) : base(side, board)
        {
            this.rearMostKey = (Board.HEIGHT - 1) * Board.WIDTH + ((Board.WIDTH - 1) / 2);
            this.origins = new Dictionary<int, Piece>{
             { 16 * Board.WIDTH + 12, null}, { 15 * Board.WIDTH + 11,null},{ 15 * Board.WIDTH + 13,null}
            ,{ 14 * Board.WIDTH + 10,null }, { 14 * Board.WIDTH + 12,null }, { 14 * Board.WIDTH + 14,null}
            ,{ 13 * Board.WIDTH + 9,null }, { 13 * Board.WIDTH + 11,null }, { 13 * Board.WIDTH + 13,null }
            ,{ 13 * Board.WIDTH + 15,null }
            };
            this.destinations = new Dictionary<int, Piece>();
        }

        private Move ChooseMove()
        {

            List<Move> moves = GetMoves();
            int index = Heuristic(moves);
            Piece piece = moves[index].GetOrigin();
            int key1 = piece.row * Board.WIDTH + piece.col;
            int moveRow = moves[index].GetRow(), moveCol = moves[index].GetCol();
            int key2 = moveRow * Board.WIDTH + moveCol;
            if (origins.ContainsKey(key1))
            {
                origins.Remove(key1);
                if (Board.initmat[moveRow, moveCol] == 3)
                    origins.Add(key2, new Piece(moveRow, moveCol));
            }
            if (destinations.ContainsKey(key2))
            {
                destinations.Remove(key2);
                if (Board.initmat[piece.row, piece.col] == 2)
                    destinations.Add(key1, new Piece(piece.row, piece.col));
            }
            return moves[index];
        }

        private State GiveStateOfGame()
        {
            State state = State.START;
            this.countEnd = 0;
            this.countMid = 0;
            this.averageRow = 0;
            int lowestRow = 0;
            this.outsidePieces = 0;
            if (origins.Count == 0)
            {
                foreach (Piece piece in pieces.Values)
                {
                    this.averageRow += piece.row;
                    if (Board.initmat[piece.row, piece.col] != 2)
                    {
                        this.outsidePieces++;
                        this.outsidePiece = piece;
                    }
                    if (piece.row > lowestRow)
                    {
                        rearMostKey = piece.row * Board.WIDTH + piece.col;
                        lowestRow = piece.row;
                    }
                    if (piece.row > Board.HEIGHT / 2)
                        countMid++;
                    else if (piece.row < Board.HEIGHT / 2)
                        countEnd++;
                }
                this.averageRow = averageRow / pieces.Count;
                if (countMid > pieces.Count / 2)
                    return State.MIDDLE;
                if (countEnd > pieces.Count / 2)
                    return State.END;
            }
            return state;
        }

        private bool IsDestination(int row, int col)
        {
            return (Board.initmat[row, col] == 2) && (board.getPiece(row, col) == null);
        }

        public void AddDestination(int row, int col)
        {
            int key = row * Board.WIDTH + col;
            destinations.Add(key, new Piece(row, col));
        }

        public void RemoveDestination(int row, int col)
        {
            int key = row * Board.WIDTH + col;
            if (destinations.ContainsKey(key))
                destinations.Remove(key);
        }

        private int GetSMoves(List<Move> moves)
        {
            int index = -1;
            foreach (var move in moves)
            {
                index++;
                if (IsSMove(move))
                    return index;
            }
            return -1;
        }

        private int LengthOfMove(Move move)
        {
            Piece piece = move.GetOrigin();
            int moveRow = move.GetRow(), moveCol = move.GetCol();
            int x = (int)Math.Pow(Math.Abs(piece.row - moveRow), 2);
            int y = (int)Math.Pow(Math.Abs(piece.col - moveCol), 2);
            int length = (int)Math.Ceiling(Math.Sqrt(x + y));
            return length;
        }
        private int LongestJump(List<Move> moves)
        {
            int longest = 0;
            int index = -1;
            foreach (var move in moves)
            {
                Piece piece = move.GetOrigin();
                int length = LengthOfMove(move);
                if (longest == 0)
                {
                    longest = length;
                    index = moves.IndexOf(move);
                }
                else if (piece.row > move.GetRow())
                {
                    if (length > longest)
                    {
                        longest = length;
                        index = moves.IndexOf(move);
                    }
                }
            }
            return index;
        }

        private bool PieceEscaped(Move move)
        {
            Piece piece = move.GetOrigin();
            int key1 = piece.row * Board.WIDTH + piece.col;
            int moveRow = move.GetRow(), moveCol = move.GetCol();
            int key2 = moveRow * Board.WIDTH + moveCol;
            return origins.ContainsKey(key1) && !origins.ContainsKey(key2);
        }

        private bool IsSMove(Move move)
        {
            Piece piece = move.GetOrigin();
            int moveRow = move.GetRow(), moveCol = move.GetCol();
            return piece.row - 4 == moveRow && piece.col == moveCol;
        }

        private bool IsRearMost(Move move)
        {
            Piece piece = move.GetOrigin();
            int moveRow = move.GetRow();
            return piece.row * Board.WIDTH + piece.col == rearMostKey && moveRow < piece.row;
        }

        private bool IsBelowAverage(Move move)
        {
            Piece piece = move.GetOrigin();
            int moveRow = move.GetRow();
            return piece.row > this.averageRow && moveRow < piece.row;
        }

        private void ResetPoints()
        {
            this.prioritiyPoint = 5;
            this.rearMostPoint = 15;
            this.destPoint = 40;
        }
        private int GetMoveWeightStart(Move move)
        {
            int moveRow = move.GetRow(), moveCol = move.GetCol();
            int weight = weights[moveRow, moveCol];
            Piece piece = move.GetOrigin();
            if ((piece.row == 13 && piece.col == 9) || (piece.row == 13 && piece.col == 15))
                weight += (piece.row - moveRow) * prioritiyPoint;
            if (PieceEscaped(move))
                weight += (piece.row - moveRow) * prioritiyPoint;
            if (IsDestination(moveRow, moveCol))
                weight += (destinationThreshold - moveRow) * destPoint;
            if (IsSMove(move))
                weight += prioritiyPoint;
            if (IsRearMost(move))
                weight += (piece.row - moveRow) * rearMostPoint;
            return weight;
        }

        private void UpdatePointsMiddle()
        {
            this.prioritiyPoint = 10;
            this.rearMostPoint = 60;
            this.destPoint = 40;
            this.SMovePoint = prioritiyPoint * 4;
        }

        private int GetMoveWeightMiddle(Move move)
        {
            int moveRow = move.GetRow(), moveCol = move.GetCol();
            Piece piece = move.GetOrigin();
            int weight = weights[moveRow, moveCol];
            if (IsRearMost(move) && weight > 0)
                weight += (piece.row - moveRow) * rearMostPoint;
            else if (IsBelowAverage(move) && weight > 0)
                weight += (piece.row - this.averageRow) * belowAvgFactor * prioritiyPoint;
            if (IsSMove(move))
                weight += SMovePoint;
            if (piece.row < Board.HEIGHT / 4 && moveRow > piece.row)
                weight -= (moveRow - piece.row) * prioritiyPoint;
            int deviation = 0;
            foreach (KeyValuePair<int, Piece> p in pieces)
            {
                int row = p.Value.row, col = p.Value.col;
                int xDev = (int)Math.Pow(Math.Abs(row - piece.row), 2);
                int yDev = (int)Math.Pow(Math.Abs(col - piece.col), 2);
                int dev = (int)Math.Sqrt(xDev + yDev);
                deviation += dev;
            }
            weight += devFactor / deviation;
            return weight;
        }

        private void UpdatePointsEnd()
        {
            this.prioritiyPoint = 10;
            this.rearMostPoint = 80;
            this.destPoint = 80;
            this.SMovePoint = prioritiyPoint * 4;
        }

        private int GetMoveWeightEnd(Move move)
        {
            int moveRow = move.GetRow(), moveCol = move.GetCol();
            int weight = weights[moveRow, moveCol];
            Piece piece = move.GetOrigin();
            if (IsRearMost(move) && weight > 0)
                weight += (piece.row - moveRow) * rearMostPoint;
            if (IsSMove(move))
                weight += SMovePoint;
            if (Board.initmat[piece.row, piece.col] == 2)
            {
                if (moveRow < piece.row && countEnd == pieces.Count)
                    weight += (piece.row - moveRow) * compressionPoint;
                else if (moveRow > piece.row || Board.initmat[moveRow, moveCol] != 2)
                    weight += avoidPoint;
            }
            else if (IsDestination(moveRow, moveCol))
                weight += (destinationThreshold - moveRow) * 2 * destPoint;
            else
            {
                if (this.outsidePieces == 1 && piece.row == this.outsidePiece.row && piece.col == this.outsidePiece.col)
                {
                    Move newMove = new Move(new Piece(moveRow, moveCol), destinations.First().Value.row, destinations.First().Value.col);
                    weight += destPoint / LengthOfMove(newMove);
                }
                if (CheckNextMove(move))
                    weight += 2 * destPoint;
            }
            return weight;
        }

        private bool CheckNextMove(Move move)
        {
            bool flag = false;
            Piece originPiece = move.GetOrigin();
            int moveRow = move.GetRow(), moveCol = move.GetCol();
            Piece temp = new Piece(moveRow, moveCol, originPiece.side);
            int originKey = originPiece.row * Board.WIDTH + originPiece.col;
            int tempKey = moveRow * Board.WIDTH + moveCol;
            pieces.Remove(originKey);
            pieces.Add(tempKey, temp);
            foreach (KeyValuePair<int, Piece> dest in this.destinations)
            {
                int row = dest.Value.row, col = dest.Value.col;
                if (board.MoveAble(temp, row, col))
                    flag = true;
            }
            pieces.Add(originKey, originPiece);
            pieces.Remove(tempKey);
            return flag;
        }

        private int Heuristic(List<Move> moves)
        {
            int index = -1;
            State state = GiveStateOfGame();
            if (state == State.START)
            {
                ResetPoints();
                index = StartStardegy(moves);
                index = (index != -1) ? index : GetSMoves(moves);
            }
            else if (state == State.MIDDLE)
            {
                UpdatePointsMiddle();
                index = MidStradegy(moves);
            }
            else if (state == State.END)
            {
                UpdatePointsEnd();
                index = EndStradegy(moves);
            }
            index = (index != -1) ? index : LongestJump(moves);
            return index;
        }

        private int StartStardegy(List<Move> moves)
        {
            int index = -1, bestWeight = 0;
            foreach (var move in moves)
            {
                Piece piece = move.GetOrigin();
                if (origins.ContainsKey(piece.row * Board.WIDTH + piece.col))
                {
                    int weight = GetMoveWeightStart(move);
                    if (weight > bestWeight)
                    {
                        bestWeight = weight;
                        index = moves.IndexOf(move);
                    }
                }
            }
            return index;
        }

        private int MidStradegy(List<Move> moves)
        {
            int index = -1;
            int bestWeight = 0;
            foreach (var move in moves)
            {
                Piece piece = move.GetOrigin();
                if (Board.initmat[piece.row, piece.col] != 2)
                {
                    int weight = GetMoveWeightMiddle(move);
                    if (weight > bestWeight)
                    {
                        bestWeight = weight;
                        index = moves.IndexOf(move);
                    }
                }
            }
            return index;
        }

        private int EndStradegy(List<Move> moves)
        {
            int index = -1;
            int bestWeight = 0;
            foreach (var move in moves)
            {
                int weight = GetMoveWeightEnd(move);
                if (weight > bestWeight)
                {
                    bestWeight = weight;
                    index = moves.IndexOf(move);
                }

            }
            return index;
        }

        public void MakeMove()
        {
            Move move = ChooseMove();
            if (move != null)
            {
                addPiece(move.GetRow(), move.GetCol(), this.side);
                removePiece(move.GetOrigin());
            }
        }


    }
}
