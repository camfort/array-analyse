program tmp
  implicit none
  integer :: i
  real, dimension(10) :: a, b, c

  do i = 1, 10
!     a(i) = b(i+1) + b(i) + c(i-1)
  end do


  do i = 1, 10
     b(i*2) = a(i*2) + a(i*2+1)     
     z = a(i+1)
     b(i) = z + a(i)
     x = a(i)
     z = a(i+1)
     w = a(i-1)
     y = x + z + z + w + a(i-1) + a(i-2)
     w = a(i*2)
  end do
end program
