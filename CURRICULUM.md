# Vector calculus curriculum

Completion of the Natural Number Game and single-variable calculus are assumed. There is no Lean tutorial world. Follow the prerequisite chain below; every world contains exactly six playable exercises. In each world, levels 1–2 include worked analogous examples, 3–4 are less scaffolded, 5 applies a method, and 6 synthesizes earlier ideas. Each level carries its objective, mathematical prerequisites, original explanation, formal exercise, three progressive hints, hidden instructor proof, and brief proof interpretation.

All 96 intended solutions use 14 tactics. Nine familiar NNG tools are available initially; `norm_num`, `constructor`, `linarith`, `simp`, and `ring` are introduced separately inside the mathematical progression. See TACTIC_UNLOCKS.md. Proved reusable rules expose coordinate calculations, partial derivatives, integral replacement, continuity, and limits without requiring players to manipulate finite indices, continuous linear maps, or filter implementation details. The limit and regularity names abbreviate the actual underlying Mathlib predicates. All intended solutions are also checked through the real player runner in Regular mode with a fresh inventory.

## 01. Vector Workshop (`Vectors`)

Prerequisites: Real arithmetic; vectors in three-dimensional space. 

1. **Coordinates:** Construct a vector and extract its components.
2. **Adding and scaling:** Compute a linear combination coordinate by coordinate.
3. **The dot product:** Evaluate the coordinate formula for an inner product.
4. **Orthogonality and length:** Check perpendicularity and a squared Euclidean length.
5. **Crossing directions:** Compute a cross product and verify perpendicularity.
6. **Boss: resolve a vector:** Compute a projection and show its remainder is orthogonal.

## 02. Space Explorer (`SpaceExplorer`)

Prerequisites: Vector Workshop; parametric lines, normals, and quadratic equations. Complete Vector Workshop.

1. **A point on a line:** Supply a parameter witnessing line membership.
2. **A plane from a normal:** Verify a plane equation from its point-normal definition.
3. **Line meets plane:** Find a point satisfying both geometric constraints.
4. **Distance to a plane:** Evaluate the normal-distance formula with a nonzero normal.
5. **A paraboloid and its traces:** Recognize an elliptic paraboloid and compute two traces.
6. **Boss: three points:** Build a nondegenerate plane through three points.

## 03. Curve Navigator (`CurveNavigator`)

Prerequisites: Vector algebra; single-variable differentiation and integration. Complete Space Explorer.

1. **Endpoints of a curve:** Evaluate a polynomial curve at its parameter endpoints.
2. **Differentiate a curve:** Compute the component derivatives of a vector curve.
3. **Motion at an instant:** Calculate velocity, acceleration, and speed at a regular point.
4. **Arc length of a segment:** Integrate the speed of a regular curve on ordered bounds.
5. **Turning on the circle:** Compute a unit tangent and curvature at a circle point.
6. **Boss: the helix:** Combine endpoints, velocity, and speed for a spatial curve.

## 04. Multivariable Landscapes (`MultivariableLandscapes`)

Prerequisites: Domains, level sets, single-variable limits and continuity. Complete Curve Navigator.

1. **A constrained domain:** Express and verify a domain with explicit inequalities.
2. **A level set:** Verify that a point lies on a specified level surface.
3. **Polynomial continuity:** Prove joint continuity of a polynomial in three variables.
4. **A limit from continuity:** Evaluate a multivariable limit using continuity.
5. **Two paths disagree:** Disprove a common limit by uniqueness along two paths.
6. **Boss: repair the origin:** Prove continuity of a separately defined extension at the origin.

## 05. Partial Derivative Lab (`PartialDerivativeLab`)

Prerequisites: Joint continuity; scalar derivatives; planes and normals. Complete Multivariable Landscapes.

1. **Hold y fixed:** Compute the first x partial derivative.
2. **Hold x fixed:** Compute the first y partial derivative.
3. **Second derivatives:** Differentiate an already computed first partial.
4. **Mixed partials agree:** Verify mixed partial equality for an explicitly smooth polynomial.
5. **A tangent approximation:** Construct the affine approximation and bound its exact error.
6. **Boss: an implicit tangent plane:** Use a regular gradient to identify a tangent plane.

## 06. Gradient Mountain (`GradientMountain`)

Prerequisites: Partial derivatives; unit directions; chain rule and matrices. Complete Partial Derivative Lab.

1. **Assemble a gradient:** Compute a gradient from coordinate partial derivatives.
2. **A unit direction:** Compute a total directional derivative with a unit-direction assumption.
3. **Along a parametrized path:** Apply the scalar chain rule to a composite along a path.
4. **A Jacobian matrix:** Compute entries of the derivative matrix of a vector map.
5. **The ascent bound:** Prove a sharp bound for a gradient dotted with a unit direction.
6. **Boss: tangent to a level set:** Relate a level-set equation, its gradient, and tangent directions.

## 07. Optimization Arena (`OptimizationArena`)

Prerequisites: First and second partial derivatives; compact regions; elementary inequalities. Complete Gradient Mountain.

1. **A critical point:** Find all critical points of a quadratic function.
2. **Positive second variation:** Classify the quadratic minimum using its positive second variation.
3. **Saddle witnesses:** Exhibit both upward and downward directions arbitrarily near a saddle.
4. **Interior and boundary:** Compare global values over a closed disk, including its boundary.
5. **Lagrange equations:** Solve the Lagrange multiplier system and find both candidates.
6. **Boss: a global constrained optimum:** Prove a feasible point attains a global optimum.

## 08. Double Integral Valley (`DoubleIntegralValley`)

Prerequisites: Single-variable integration; planar regions; mass and moments. Complete Optimization Arena.

1. **A rectangle:** Evaluate an iterated integral on a rectangle.
2. **A triangular region:** Translate a triangular region into equivalent bounds.
3. **Reverse the order:** Verify reversed bounds by evaluating both integrals.
4. **Area and volume:** Compute area and the volume below a constant roof.
5. **A lamina centroid:** Compute mass and a normalized first moment.
6. **Boss: a triangular lamina:** Combine variable bounds, mass, and a first moment.

## 09. Triple Integral Caverns (`TripleIntegralCaverns`)

Prerequisites: Double integrals; solid bounds; density and moments. Complete Double Integral Valley.

1. **A rectangular box:** Evaluate a triple iterated integral on a box.
2. **Bounds for a solid:** Express a sloping-roof solid with explicit bounds.
3. **Volume below a roof:** Calculate volume using a variable upper bound.
4. **Variable density:** Compute mass from a nonconstant density.
5. **A first moment:** Integrate position times density.
6. **Boss: the center of a solid:** Compute positive mass and three normalized moments.

## 10. Coordinate Portal (`CoordinatePortal`)

Prerequisites: Multiple integrals; determinants; trigonometric identities. Complete Triple Integral Caverns.

1. **Polar identities:** Verify the radial identity for polar coordinates.
2. **Polar area factor:** Derive the polar determinant and integrate the unit disk area density.
3. **Cylindrical volume:** Evaluate a correctly weighted cylindrical-coordinate integral.
4. **Spherical volume:** Evaluate the spherical volume density on its standard domain.
5. **A nonpolar Jacobian:** Compute a determinant for a linear coordinate transformation.
6. **Boss: an absolute Jacobian:** Verify a change-of-variables equality with an orientation-reversing map.

## 11. Vector Field Observatory (`VectorFieldObservatory`)

Prerequisites: Gradients, partial derivatives, and three-dimensional vectors. Complete Coordinate Portal.

1. **Compare two fields:** Evaluate and distinguish vector fields at a point.
2. **Recognize a gradient:** Verify that a field has a specified potential.
3. **Divergence:** Compute a field divergence using the appropriate coordinate derivatives.
4. **Curl:** Compute an oriented curl from coordinate partial derivatives.
5. **Two differential identities:** Verify curl-of-gradient and divergence-of-curl for explicit smooth fields.
6. **Boss: construct a potential:** Supply a potential and verify it globally.

## 12. Path Integral Trails (`PathIntegralTrails`)

Prerequisites: Regular parametrized curves; vector fields; the fundamental theorem of calculus. Complete Vector Field Observatory.

1. **Choose an orientation:** Parametrize a line segment with specified initial and final points.
2. **A weighted wire:** Evaluate a scalar line integral with arc-length weight.
3. **Work along a curve:** Integrate a vector field dotted with the curve velocity.
4. **Reverse orientation:** Show that reversing oriented integration negates work.
5. **Apply the endpoint theorem:** Use an established fundamental theorem for line integrals.
6. **Boss: path independence:** Use a potential to compare two paths and compute their common work.

## 13. Green’s Garden (`GreensGarden`)

Prerequisites: Planar line integrals; double integrals; positive orientation. Complete Path Integral Trails.

1. **A positive boundary:** Verify endpoints of counterclockwise square edges.
2. **Circulation by edges:** Evaluate circulation directly along a closed boundary.
3. **The interior integrand:** Compute the matching planar curl integral.
4. **Green for a shear field:** Apply a proved circulation-form Green special case.
5. **Green in flux form:** Verify outward planar flux equals the divergence integral.
6. **Boss: area from the boundary:** Recover enclosed area from a boundary circulation.

## 14. Surface Expedition (`SurfaceExpedition`)

Prerequisites: Cross products; partial derivatives; double integration. Complete Green’s Garden.

1. **Parametrize a surface:** Verify that a patch lies in a specified surface.
2. **Tangents and normal:** Compute the two parameter tangents and their oriented cross product.
3. **Area factor:** Compute the Euclidean surface-area density.
4. **A scalar surface integral:** Integrate a scalar density with the area factor.
5. **Oriented flux:** Integrate a vector field against an oriented area vector.
6. **Boss: reverse the patch:** Compare equal scalar area and opposite oriented flux.

## 15. Stokes Summit (`StokesSummit`)

Prerequisites: Curl; positively oriented boundaries; parametrized surface flux. Complete Surface Expedition.

1. **The boundary of a patch:** Determine all four oriented boundary traces of a parametrized patch.
2. **Match orientations:** Verify the normal and oriented top boundary agree.
3. **Curl through a patch:** Compute the curl flux integrand in Stokes’ formula.
4. **The boundary calculation:** Evaluate circulation with the orientation induced by the surface.
5. **Apply Stokes: square patch:** Apply an established Stokes special-case family.
6. **Boss: choose a simpler surface:** Justify replacing a graph by a planar patch with the same oriented boundary.

## 16. Gauss Citadel (`GaussCitadel`)

Prerequisites: Divergence; oriented surface flux; triple integrals; integral theorem special cases. Complete Stokes Summit.

1. **An outward closed boundary:** Verify outward orientation on all six cube faces.
2. **Divergence in the solid:** Integrate a field divergence over the cube.
3. **Flux by boundary pieces:** Compute flux directly on the six outward-oriented faces.
4. **Apply Gauss on a cube:** Apply a proved divergence-theorem family with verified orientation.
5. **Recover a missing face:** Deduce an unknown flux from the closed-boundary total.
6. **Final boss: three integral bridges:** Combine justified special cases of Green, Stokes, and Gauss.

The advanced families are deliberately restricted: see STATUS.md before interpreting a calculation as an application of a general theorem.
