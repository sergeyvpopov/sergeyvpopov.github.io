# ---------------------------------------------------------------------------
# phi_contour_paper_notation.R
#
# Replicates Figure 1 of Appendix B. Concretely:
#
#   X       : the 2x3 ownership matrix (row 1 = artist 1, row 2 = artist 2;
#             columns = collectors 1,2,3)
#   A       : [I - alpha*beta*X^T X]^{-1}, the 3x3 resolvent, via direct
#             matrix inversion (solve())
#   B       : (1-alpha)*v + alpha*(1-beta)*X^T theta
#   R       : A %*% B
#   q       : (1-beta)*theta + beta*X %*% R
#   G^i_jk  : alpha*q[i]*(A[j,j]-A[k,k]) + alpha*beta*(R[j]-R[k])*((A%*%x_i)[j]+(A%*%x_i)[k])
#   Phi     : sum over feasible (i,j,k), j!=k, X[i,k]>0, of max(0,G^i_jk)^2
#
# The free parameters plotted are X[1,1] and X[2,1];
# X[1,2] and X[2,2]  are minimized out at each grid point;
# X[1,3], X[2,3] are fixed by each artist's row summing to
# Y_i = 2.
#
# Base R only (stats, graphics, grDevices) -- no external packages required.
# ---------------------------------------------------------------------------

alpha <- 0.3
beta  <- 0.1
theta <- c(1, -5)
v     <- c(1, 1, -5)

# ---------------------------------------------------------------- model
model_XABRq <- function(X) {
  # X: 2x3 matrix (rows = artists, columns = collectors)
  A <- solve(diag(3) - alpha*beta*(t(X) %*% X))
  B <- (1-alpha)*v + alpha*(1-beta)*(t(X) %*% theta)
  R <- A %*% B
  q <- (1-beta)*theta + beta*(X %*% R)
  list(A = A, B = B, R = as.vector(R), q = as.vector(q))
}

# G^i_{j,k}: i in {1,2} (1=artist1,2=artist2), j,k in {1,2,3}, j != k
G_val <- function(M, X, i, j, k) {
  xi <- X[i, ]                    # i-th row of X (artist i's holdings)
  Ax <- as.vector(M$A %*% xi)
  alpha*M$q[i]*(M$A[j,j]-M$A[k,k]) + alpha*beta*(M$R[j]-M$R[k])*(Ax[j]+Ax[k])
}

Phi_val <- function(X, tol = 1e-9) {
  M <- model_XABRq(X)
  total <- 0
  for (i in 1:2) {
    for (k in 1:3) {
      if (X[i,k] <= tol) next
      for (j in 1:3) {
        if (j == k) next
        g <- G_val(M, X, i, j, k)
        if (g > 0) total <- total + g^2
      }
    }
  }
  total
}

# ---------------------------------------------------------------- self-check
X_star <- matrix(c(1,1,0, 1,1,0), nrow = 2, byrow = TRUE)
phi_at_Xstar <- Phi_val(X_star)

a1_check <- 0.9887640449438202
X_check <- matrix(c(a1_check, 1, 2-a1_check-1,
                     a1_check, 1, 2-a1_check-1), nrow = 2, byrow = TRUE)
phi_checkpoint <- Phi_val(X_check)

cat(sprintf("Self-check: Phi(X*) = %.3e  (expect ~0)\n", phi_at_Xstar))
cat(sprintf("Self-check: Phi(checkpoint) = %.6f  (expect 0.030118)\n", phi_checkpoint))
if (abs(phi_at_Xstar) > 1e-8 || abs(phi_checkpoint - 0.0301176) > 1e-4) {
  stop("Self-check FAILED -- model_XABRq/G_val/Phi_val has a bug. Do not trust the plot.")
}
cat("Self-check passed.\n\n")

# also print the two G values the paper itself quotes, as an extra cross-check
M_star <- model_XABRq(X_star)
G1_31 <- G_val(M_star, X_star, 1, 3, 1)   # G^1_{3,1}
G2_31 <- G_val(M_star, X_star, 2, 3, 1)   # G^2_{3,1}
cat(sprintf("G^1_3,1 = %.6f  (paper: strictly negative)\n", G1_31))
cat(sprintf("G^2_3,1 = %.6f  (paper: strictly negative)\n\n", G2_31))

# ---------------------------------------------------------------- outer/inner grid
n_outer <- 61      # 60 intervals -> X[1,1]=X[2,1]=1 lands EXACTLY on a grid node
n_inner <- 21

a1_vals <- seq(0, 2, length.out = n_outer)   # X[1,1] values (plotted, x-axis)
b1_vals <- seq(0, 2, length.out = n_outer)   # X[2,1] values (plotted, y-axis)
stopifnot(abs(a1_vals[(n_outer+1)/2] - 1.0) < 1e-9)

a2_grid <- seq(0, 2, length.out = n_inner)   # X[1,2] values (minimized out)
b2_grid <- seq(0, 2, length.out = n_inner)   # X[2,2] values (minimized out)

Phi_min <- matrix(NA_real_, nrow = n_outer, ncol = n_outer)  # [row=X21 index, col=X11 index]

cat("Computing profile-minimized Phi over (X11,X21) grid (real matrix inversion per point)...\n")
t0 <- Sys.time()
for (ia in seq_along(a1_vals)) {
  x11 <- a1_vals[ia]
  for (ib in seq_along(b1_vals)) {
    x21 <- b1_vals[ib]
    best <- Inf
    for (x12 in a2_grid) {
      x13 <- 2 - x11 - x12
      if (x13 < -1e-9) next
      x13 <- min(max(x13, 0), 2)
      for (x22 in b2_grid) {
        x23 <- 2 - x21 - x22
        if (x23 < -1e-9) next
        x23 <- min(max(x23, 0), 2)
        X <- matrix(c(x11,x12,x13, x21,x22,x23), nrow = 2, byrow = TRUE)
        val <- Phi_val(X)
        if (val < best) best <- val
      }
    }
    if (is.finite(best)) Phi_min[ib, ia] <- best
  }
  if (ia %% 10 == 0) cat(sprintf("  X11 index %d/%d  elapsed %.1fs\n", ia, n_outer, as.numeric(Sys.time()-t0, units="secs")))
}
cat(sprintf("total time: %.1fs\n", as.numeric(Sys.time()-t0, units="secs")))

mid <- (n_outer+1)/2
cat(sprintf("Phi_min at exact (X11,X21)=(1,1): %.3e\n", Phi_min[mid, mid]))

# ---------------------------------------------------------------- smoothing (separable Gaussian, log-space)
gaussian_kernel_1d <- function(sigma, radius = ceiling(3*sigma)) {
  x <- -radius:radius
  k <- exp(-(x^2)/(2*sigma^2))
  k/sum(k)
}

smooth_1d <- function(x, kernel) {
  r <- (length(kernel)-1)/2
  n <- length(x)
  xpad <- c(rev(x[1:r]), x, rev(x[(n-r+1):n]))
  out <- numeric(n)
  for (t in 1:n) out[t] <- sum(xpad[t:(t+2*r)] * kernel)
  out
}

smooth_2d <- function(M, sigma) {
  kernel <- gaussian_kernel_1d(sigma)
  M2 <- t(apply(M, 1, smooth_1d, kernel = kernel))
  M3 <- apply(M2, 2, smooth_1d, kernel = kernel)
  M3
}

floor_val <- 1e-6
logZ <- log10(Phi_min + floor_val)
sigma <- 1.2
logZ_s <- smooth_2d(logZ, sigma)
Phi_s <- pmax(10^logZ_s - floor_val, 0)

# ---------------------------------------------------------------- plot
png("phi_contour.png", width = 1400, height = 1200, res = 160)

filled.contour(
  x = a1_vals, y = b1_vals, z = t(logZ_s),
  color.palette = function(n) hcl.colors(n, "Viridis"),
  xlab = expression(X[11] ~ "  (artist 1, collector 1)"),
  ylab = expression(X[21] ~ "  (artist 2, collector 1)"),
  plot.axes = {
    axis(1); axis(2)
    contour(a1_vals, b1_vals, t(Phi_s),
            levels = c(1e-5,1e-4,1e-3,3e-3,1e-2,3e-2,6e-2,1e-1),
            add = TRUE, col = "white", labcex = 0.6, method = "edge")
    points(1, 1, pch = 8, col = "red", cex = 2.2, lwd = 2)
    legend("bottomleft", legend = "X* (unique zero of Phi)", pch = 8, col = "red", bty = "n")
  }
)
dev.off()
cat("saved phi_contour.png\n")