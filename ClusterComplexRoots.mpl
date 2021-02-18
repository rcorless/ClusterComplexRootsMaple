# ClusterComplexRoots.mpl
#
# clusteredList := ClusterComplexRoots( rootList, tolerance=s, MaxOrder=M );
#
# Take a list rootList of complex numbers and cluster them
# according to apparent multiplicity.
#
# This routine is heuristic (the problem is hard) and is intended
# to work only up to the given maximum order (default MaxOrder is 3)
#
# The routine uses distances and a fuzz factor F[m] and only considers
# neighbouring points up to about |r[i]-r[j]| <= F[m]*s^(1/m) to be
# possible candidates for a cluster; it also uses approximate 
# angle symmetry, looking for angles between adjacent roots to be
# approximately 2*Pi/m .
#
# The returned clusteredList will be a list of pairs [r,m] where
# r is the mean of the original cluster of m roots.
# -----------------------------------------------------------------------------
# (c) Robert M. Corless and Leili Rafiee Sevyeri 2020 (MIT Release licence)
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.
# -------------------------------------------------------------------------------

ClusterComplexRoots := proc( rootList::list, 
                            {tolerance::numeric := Float(1,2-Digits)}, 
                            {MaxOrder::nonnegint := 3}, $ )
    local anglesequal, 
          c, closeenough, closeNeighbours, clustered, combos, countem, 
          DistanceMatrix, exactangle, finished_combos, Fuzz,
          i, j, k, m, max_radius, mean, 
          n, neighbours, notInAcluster, nroots, 
          phasedifference, phases, phaseorder, 
          r, radius, trialcluster, trialindices, unseen_m;


    # Safety factors for distance computations.
    # They essentially replace the factor m!*B(r)/(D@@m)(f)(r)
    # which connects the root semimetric with the coefficient
    # metric; in this implementation, no account is taken of
    # the problem in this way (but it can be done in a post-
    # processing validation step).
    Fuzz := Array(2..MaxOrder);
    for m from 2 to MaxOrder do
      Fuzz[m] := evalf(2^(1/m));
    od;

    # Process small rootlists
    nroots := numelems( rootList );
    if nroots=0 then
      error "cannot cluster an empty list of roots";
    elif nroots=1 then
      # Return a cluster of 1
      return [[rootList[1],1]];
    end if;

    # nroots>=2 from now on
    # We will need distances between roots
    # -- to identify "close" roots
    # -- to ignore "far" roots
    DistanceMatrix := Matrix( nroots, nroots, 'shape'='symmetric' );
    for i to nroots do
      for j to nroots do
        DistanceMatrix[i,j] := evalf( abs( rootList[i] - rootList[j]) ) ;
      od;
    od;

    # We order neighbours from nearest to farthest
    neighbours := Array(1..nroots);
    for i to nroots do
      neighbours[i] := sort( [seq(DistanceMatrix[i,j],j=1..nroots)], 
                              'output'='permutation');
      # neighbours[i] should be a list of integers such that
      # the nearest root to rootList[i] should be 
      # rootList[neighbours[i][1]] (itself), the next nearest should be
      # rootList[neighbours[i][2]], and so on
    od;

    # Now begin the clustering.  We start with no clustered roots at all.
    clustered := NULL;
    # The notInAcluster roots are, at the start, all of them.
    # This states that we *assume* these are not in any m-cluster
    # for m > MaxOrder.
    notInAcluster := seq(k,k=1..nroots); 
    for m from MaxOrder by -1 to 2 do
      # The sequence "notInAcluster" can shrink inside this loop
      # The list unseen_m tracks which roots we haven't yet
      # considered for any cluster at level m
      unseen_m := [notInAcluster]; # never any duplicates
      notInAcluster := NULL; # means known not to be part of any m-cluster
      # Assert nroots in clustered, notInAcluster,unseen_m +0(i)
      while numelems(unseen_m) >= m do
        # Checking for m-cycles over all elements of unseen_m
        i := unseen_m[1];
        # print("considering root", i, "or", rootList[i], "for cycles of length", m);
        unseen_m := unseen_m[2..numelems(unseen_m)]; # Assert nroots-1 + 1(i)
        # the root under consideration is rootList[i]
        # we try to find an m-cluster with this in it
        # No need to consider roots farther away than 
        # twice the distance to the centre of any m-cluster
        # to this tolerance
        k := nroots;
        while k > 0 and 
              DistanceMatrix[i,neighbours[i][k]] > 2*Fuzz[m]*tolerance^(1/m) do
          k := k-1;
        od;
        closeNeighbours := {seq(neighbours[i][j], j=2..k)}; # might be empty
        closeNeighbours := closeNeighbours intersect convert(unseen_m,set);
        closeNeighbours := convert(closeNeighbours,list);
        # examine all sets of m-1 close neighbours
        n := numelems(closeNeighbours); # <= k-1
        if n>=m-1 then
          # Now look at all possible choices of m-clusters
          # from the set of close neighbours
          combos := Iterator:-Combination( n, m-1 ); # at least 1
          finished_combos := false;
          for c in combos do
            # Iterator:-Combination indexes from 0 but lists index from 1
            trialindices := [i,seq(closeNeighbours[c[k]+1],k=1..m-1)];
            trialcluster := seq( rootList[k], k in trialindices );
            mean := evalf( add( r, r in [trialcluster] )/m );
            # Check the distances
            closeenough := true;
            max_radius := 0;
            for r in trialcluster do
              radius := abs(r-mean);
              max_radius := max( max_radius, radius ); 
              if radius > Fuzz[m]*tolerance^(1/m) then
                closeenough := false;
                break;
              end if;
            od;
            if closeenough then
              # Now check the angles
              # May be nonsense if max_radius=0
              anglesequal := true;
              if max_radius >= Float(1,1-Digits) then
                phases := [seq( argument( trialcluster[k]-mean), k=1..m) ];
                phaseorder := sort( phases, 'output'='permutation' );
                trialcluster := [seq( trialcluster[phaseorder[k]], k=1..m)];
                phases := [seq( phases[phaseorder[k]], k=1..m)];
                # Now check if all the angles are approximately equal
                exactangle := evalf(2*Pi/m);
                for k from 2 to m do
                  phasedifference := phases[k]-phases[k-1];
                  # Heuristic: what constitutes approximately equal angle?
                  if 0.75*exactangle > phasedifference or
                      phasedifference > 1.25*exactangle then
                    anglesequal := false;
                    break; # no need to consider this trial cluster further
                  end if;
                end do; # exit this loop on break for unequal angles
              end if;
              # closeenough is true, remember
              if anglesequal then
                # We have found a cluster of m roots
                clustered := [mean,m,trialcluster],clustered;
                # print([clustered], unseen_m);
                unseen_m := remove( k->member(k,convert(trialindices,set)), 
                                    unseen_m );
                # print("removed",trialindices,"got",unseen_m);
                # Assert nroots + 1(i)
                break; # stop considering rootList[i]
              end if;
            # else Not close enough to be a cluster.
            end if; 
            finished_combos := Rank(combos)=Number(combos);
            # Go look at the other choices of m-1 elements
          end do; # end for c in combos do; exit this loop via break for found cluster
          # stop looking at rootList[i] but keep looking for m-clusters
          if finished_combos then
            # Loop finished without finding a cluster
            notInAcluster := i,notInAcluster;
            # else We did find a cluster and have seen i
          end if;
          # print(m,"unseen_m",unseen_m);
        else
          # Not enough close neighbours to form an m-cycle
          notInAcluster := i, notInAcluster;
        end if;
      end do; # end while unseen_m has more than m elts do
      # Now look at clusters of smaller order
      for k in unseen_m do
        notInAcluster := k,notInAcluster;
      od;
      unseen_m := [];
    end do;
    # Everything left over is a 1-cluster
    notInAcluster := [notInAcluster];
    return [clustered, seq( [rootList[notInAcluster[k]],1], 
                            k=1..numelems(notInAcluster)) ];
  end proc:
