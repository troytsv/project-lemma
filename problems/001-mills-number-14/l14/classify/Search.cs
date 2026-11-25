using System;
using System.Collections.Generic;
using System.Numerics;

public static class LemmaSupportSearch
{
    private const int VertexCount = 14;
    private const double Epsilon = 1e-9;

    private static double Match(IReadOnlyList<int> edges)
    {
        int count = edges.Count;
        int rhs = count + VertexCount;
        double[,] tableau = new double[VertexCount + 1, rhs + 1];

        for (int vertex = 0; vertex < VertexCount; vertex++)
        {
            for (int edge = 0; edge < count; edge++)
                tableau[vertex, edge] = (edges[edge] >> vertex) & 1;
            tableau[vertex, count + vertex] = 1;
            tableau[vertex, rhs] = 4;
        }
        for (int edge = 0; edge < count; edge++)
            tableau[VertexCount, edge] = -1;

        for (int step = 0; step < 200; step++)
        {
            int enter = -1;
            for (int column = 0; column < rhs; column++)
                if (tableau[VertexCount, column] < -Epsilon &&
                    (enter == -1 || tableau[VertexCount, column] < tableau[VertexCount, enter]))
                    enter = column;
            if (enter == -1)
                return tableau[VertexCount, rhs];

            int leave = -1;
            double leastRatio = double.PositiveInfinity;
            for (int row = 0; row < VertexCount; row++)
            {
                double coefficient = tableau[row, enter];
                if (coefficient > Epsilon && tableau[row, rhs] / coefficient < leastRatio - Epsilon)
                {
                    leastRatio = tableau[row, rhs] / coefficient;
                    leave = row;
                }
            }
            if (leave == -1)
                throw new InvalidOperationException("The matching objective must be bounded.");

            double pivot = tableau[leave, enter];
            for (int column = 0; column <= rhs; column++)
                tableau[leave, column] /= pivot;
            for (int row = 0; row <= VertexCount; row++)
            {
                double multiplier = tableau[row, enter];
                if (row == leave || Math.Abs(multiplier) < Epsilon)
                    continue;
                for (int column = 0; column <= rhs; column++)
                    tableau[row, column] -= multiplier * tableau[leave, column];
            }
        }
        return double.NaN;
    }

    private static List<int> ProjectivePlane()
    {
        var lines = new List<int> { (1 << 9) | (1 << 10) | (1 << 11) | (1 << 12) };
        for (int intercept = 0; intercept < 3; intercept++)
        {
            lines.Add((1 << 12) | (7 << (3 * intercept)));
            for (int slope = 0; slope < 3; slope++)
            {
                int line = 1 << (9 + slope);
                for (int x = 0; x < 3; x++)
                    line |= 1 << (3 * x + (slope * x + intercept) % 3);
                lines.Add(line);
            }
        }
        return lines;
    }

    public static void Run(int seed, int restarts, int steps)
    {
        var random = new Random(seed);
        var all = new List<int>[8];
        for (int rank = 4; rank <= 7; rank++)
            all[rank] = new List<int>();
        for (int mask = 1; mask < 1 << VertexCount; mask++)
        {
            int rank = BitOperations.PopCount((uint)mask);
            if (rank >= 4 && rank <= 7)
                all[rank].Add(mask);
        }
        List<int> plane = ProjectivePlane();
        if (Math.Abs(Match(plane) - 13) > Epsilon || Math.Abs(Match(new[] { 15 }) - 4) > Epsilon)
            throw new InvalidOperationException("The matching self-check failed.");

        double best = 13;
        double bestWithoutOriginalPlane = 0;
        int[] bestAlternative = null;
        int evaluated = 0;
        int stalled = 0;
        for (int restart = 0; restart < restarts; restart++)
        {
            var current = new List<int>(plane);
            double score = 13;
            for (int step = 0; step < steps; step++)
            {
                var next = new List<int>(current);
                int remove = Math.Min(next.Count, random.Next(100) < 80 ? 1 : random.Next(2, 5));
                for (int index = 0; index < remove; index++)
                    next.RemoveAt(random.Next(next.Count));

                while (next.Count < VertexCount)
                {
                    int selected = 0;
                    for (int trial = 0; trial < 210; trial++)
                    {
                        var pool = all[random.Next(100) < 60 ? 4 : random.Next(5, 8)];
                        int candidate = pool[random.Next(pool.Count)];
                        if (next.TrueForAll(edge => (edge & candidate) != 0 && edge != candidate))
                        {
                            selected = candidate;
                            break;
                        }
                    }
                    if (selected == 0)
                        break;
                    next.Add(selected);
                }
                double nextScore = Match(next);
                if (double.IsNaN(nextScore))
                {
                    stalled++;
                    continue;
                }

                evaluated++;
                if (nextScore > bestWithoutOriginalPlane + Epsilon &&
                    !plane.TrueForAll(line => next.Contains(line)))
                {
                    bestWithoutOriginalPlane = nextScore;
                    bestAlternative = next.ToArray();
                }
                if (nextScore > best + Epsilon)
                {
                    best = nextScore;
                    Console.WriteLine($"improved W = {best:G17}, masks = {string.Join(",", next)}");
                }
                double temperature = restart % 3 == 0 ? 0.035 : restart % 3 == 1 ? 0.09 : 0.16;
                if (nextScore >= score - Epsilon || random.NextDouble() < Math.Exp((nextScore - score) / temperature))
                {
                    current = next;
                    score = nextScore;
                }
            }
        }
        Console.WriteLine($"seed = {seed}, evaluated = {evaluated}, stalled = {stalled}, best W = {best:G17}");
        if (bestAlternative != null)
            Console.WriteLine($"best W without the original plane = {bestWithoutOriginalPlane:G17}, masks = {string.Join(",", bestAlternative)}");
    }
}
